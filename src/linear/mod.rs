use std::iter::FromIterator;
use std::vec;
use std::vec::Vec;

use smallvec::SmallVec;

use crate::{Allocation, Block, Edit, Function, HwRegSet, Inst, InstPosition, InstRange, MachineEnv, Operand, OperandConstraint, OperandKind, OperandPos, Output, PReg, ProgPoint, RegAllocError, RegClass, VReg};
use crate::linear::allocation_state::AllocationState;

mod allocation_state;

struct BlockParams {
    block_params_offsets: Vec<usize>,
    block_params: Vec<Allocation>,
}

impl BlockParams {
    #[inline]
    fn new<F: Function>(func: &F) -> Self {
        let mut block_params_offsets = Vec::with_capacity(func.num_blocks() + 1);
        let mut block_params = 0;
        for block in 0..func.num_blocks() {
            block_params_offsets.push(block_params);
            block_params += func.block_params(Block::new(block)).len();
        }
        block_params_offsets.push(block_params);
        let block_params = vec![Allocation::none(); block_params];

        Self {
            block_params_offsets,
            block_params,
        }
    }

    #[inline]
    fn block_param_allocations(&self, block: Block) -> &[Allocation] {
        let index = block.index();
        let offset = self.block_params_offsets[index];
        let end = self.block_params_offsets[index + 1];

        &self.block_params[offset..end]
    }

    #[inline]
    fn block_param_allocations_mut(&mut self, block: Block) -> &mut [Allocation] {
        let index = block.index();
        let offset = self.block_params_offsets[index];
        let end = self.block_params_offsets[index + 1];

        &mut self.block_params[offset..end]
    }
}

struct Env<'a, F: Function> {
    func: &'a F,
    mach_env: &'a MachineEnv,
    allocation_state: AllocationState<'a, F>,
    // Allocations
    inst_alloc_offsets: Vec<u32>,
    allocs: Vec<Allocation>,
    edits: Vec<(ProgPoint, Edit)>,
    // Blockparams
    block_params: BlockParams,
    // State
    current_block: Block,
    current_block_inst_range: InstRange,
    current_inst: Inst,
    // Helper
    regs_by_class: [HwRegSet; 3],
}

impl<'a, F: Function> Env<'a, F> {
    #[inline]
    fn new(func: &'a F, mach_env: &'a MachineEnv) -> Self {
        let allocation_state = AllocationState::new(func, mach_env);
        let mut inst_alloc_offsets = Vec::with_capacity(func.num_insts());
        let mut allocs = 0;
        for inst in 0..func.num_insts() {
            inst_alloc_offsets.push(allocs);
            allocs += func.inst_operands(Inst::new(inst)).len() as u32;
        }
        let allocs = vec![Allocation::none(); allocs as usize];
        let block_params = BlockParams::new(func);
        let edits = Vec::with_capacity(func.num_insts() * 4);
        let current_block = Block::new(0);
        let current_block_inst_range = func.block_insns(current_block);
        let current_inst = current_block_inst_range.last();

        let mut regs_by_class = [HwRegSet::empty(); 3];
        for reg_class in [RegClass::Int, RegClass::Float, RegClass::Vector] {
            for &preg in mach_env.preferred_regs_by_class[reg_class as usize].iter() {
                regs_by_class[reg_class as usize].add(preg);
            }
            for &preg in mach_env.non_preferred_regs_by_class[reg_class as usize].iter() {
                regs_by_class[reg_class as usize].add(preg);
            }
        }

        Self {
            func,
            mach_env,
            allocation_state,
            inst_alloc_offsets,
            allocs,
            edits,
            block_params,
            current_block,
            current_block_inst_range,
            current_inst,
            regs_by_class,
        }
    }

    fn run(mut self) -> Result<Output, RegAllocError> {
        let mut allocated = vec![false; self.func.num_blocks()];
        for block in 0..self.func.num_blocks() {
            let block = Block::new(block);
            if self.func.block_succs(block).len() == 0 {
                self.run_internal(block, &mut allocated)?;
                break;
            }
        }

        self.edits.reverse();
        self.edits.sort_by_key(|(point, _)| *point);

        Ok(Output {
            num_spillslots: self.allocation_state.num_spillslots(),
            edits: self.edits,
            allocs: self.allocs,
            inst_alloc_offsets: self.inst_alloc_offsets,
            safepoint_slots: vec![],
            debug_locations: vec![],
            stats: Default::default(),
        })
    }

    fn run_internal(
        &mut self,
        block: Block,
        allocated: &mut Vec<bool>,
    ) -> Result<(), RegAllocError> {
        if allocated[block.index()] {
            return Ok(());
        }
        allocated[block.index()] = true;
        self.current_block = block;
        self.current_block_inst_range = self.func.block_insns(block);
        self.current_inst = self.current_block_inst_range.iter().rev().next().unwrap();
        self.allocate_block_params();
        for inst in self.current_block_inst_range.iter().rev() {
            self.current_inst = inst;
            self.allocate_operands()?;
        }
        self.generate_block_param_allocations()?;
        self.generate_block_param_edits()?;

        for &succ in self.func.block_preds(block) {
            self.run_internal(succ, allocated)?;
        }

        Ok(())
    }

    /// Generate the allocations for the parameters of the successor blocks.
    #[inline]
    fn allocate_block_params(&mut self) {
        debug_assert!(self.current_inst == self.current_block_inst_range.iter().rev().next().unwrap());
        let succs = self.func.block_succs(self.current_block);
        for (idx, &succ) in succs.iter().enumerate() {
            let params = self.func.branch_blockparams(self.current_block, self.current_inst, idx);
            for (&param, &allocation) in params.iter().zip(self.block_params.block_param_allocations(succ)) {
                self.allocation_state.allocate_vreg(self.current_inst, param, allocation);
            }
        }
    }

    #[inline]
    fn generate_block_param_edits(&mut self) -> Result<(), RegAllocError> {
        debug_assert!(self.current_inst == self.current_block_inst_range.first());
        // The registers that are used by the input parameters.
        let mut input = HwRegSet::empty();
        let allocations = self.block_params.block_param_allocations(self.current_block);
        for allocation in allocations {
            if let Some(preg) = allocation.as_reg() {
                input.add(preg);
            }
        }
        let params = self.func.block_params(self.current_block);
        'superloop: loop {
            for (&src_allocation, &vreg) in allocations.iter().zip(params) {
                let dst_allocation = self.allocation_state.get_vreg_allocation(vreg);
                if src_allocation == dst_allocation {
                    // The allocation is already correct.
                    continue;
                }

                if let Some(dst) = dst_allocation.as_reg() {
                    if !input.contains(dst) {
                        // The destination preg is not used by another parameter, we can just move the value.
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: src_allocation,
                                to: dst_allocation,
                            },
                        ));
                        continue 'superloop;
                    }
                }
            }

            for (&src_allocation, &vreg) in allocations.iter().zip(params) {
                let dst_allocation = self.allocation_state.get_vreg_allocation(vreg);
                if src_allocation == dst_allocation {
                    // The allocation is already correct.
                    continue;
                }

                if let Some(dst) = dst_allocation.as_reg() {
                    if input.contains(dst) {
                        // The destination preg is used by another parameter, we need to swap the values.
                        let scratch_reg = self.allocation_state.find_scratch_reg(dst.class(), input)
                            .ok_or(RegAllocError::TooManyLiveRegs)?;
                        // The edits are in reverse order, so we need to add them in reverse order.
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: Allocation::reg(scratch_reg),
                                to: src_allocation,
                            },
                        ));
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: src_allocation,
                                to: dst_allocation,
                            },
                        ));
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: dst_allocation,
                                to: Allocation::reg(scratch_reg),
                            },
                        ));
                        continue 'superloop;
                    }
                }
            }

            break;
        }


        Ok(())
    }

    #[inline]
    fn find_blocked_argument_slots(&self) -> Result<HwRegSet, RegAllocError> {
        debug_assert!(self.current_inst == self.current_block_inst_range.first());
        // For each predecessor block, we need to block the pregs used by the last instruction.
        // The remaining pregs will be used to allocate the arguments. If there are not enough
        // pregs for the arguments, we will use spillslots for the remaining arguments.
        // -------------------------------------------------------------------------------------
        // We start by blocking all fixed pregs.
        let preds = self.func.block_preds(self.current_block);
        let mut blocked_pregs = HwRegSet::empty();
        for &pred in preds {
            let last_inst = self.func.block_insns(pred).last();
            let operands = self.func.inst_operands(last_inst);
            for operand in operands {
                if let OperandConstraint::FixedReg(preg) = operand.constraint() {
                    blocked_pregs.add(preg);
                }
            }
        }
        // Next we try to allocate the arguments.
        for &pred in preds {
            let mut this_blocked_pregs = blocked_pregs;
            let last_inst = self.func.block_insns(pred).last();
            let operands = self.func.inst_operands(last_inst);
            for &operand in operands {
                if let OperandConstraint::FixedReg(preg) = operand.constraint() {
                    this_blocked_pregs.remove(preg);
                }
            }
            'operands: for &operand in operands {
                if let OperandConstraint::Reg = operand.constraint() {
                    let class = operand.class() as usize;
                    for preg in this_blocked_pregs.into_iter() {
                        if self.regs_by_class[class].contains_idx(preg) {
                            this_blocked_pregs.remove_idx(preg);
                            continue 'operands;
                        }
                    }

                    // We didn't find a preg, we need reserve an additional preg.
                    let mut available_pregs = self.regs_by_class[class];
                    available_pregs = available_pregs & !this_blocked_pregs;
                    blocked_pregs.add_idx(available_pregs.into_iter()
                        .next()
                        .ok_or(RegAllocError::TooManyLiveRegs)?);
                }
            }
        }

        Ok(blocked_pregs)
    }

    #[inline]
    fn generate_block_param_allocations(&mut self) -> Result<(), RegAllocError> {
        let blocked_argument_slots = self.find_blocked_argument_slots()?;
        let arguments = self.func.block_params(self.current_block);
        let block_param_allocations = self.block_params.block_param_allocations_mut(self.current_block);
        for (idx, &arg) in arguments.iter().enumerate() {
            let class = arg.class();
            let mut regs = self.regs_by_class[class as usize];
            regs = regs & !blocked_argument_slots;

            // First we try to just use the current allocation.
            let current_allocation = self.allocation_state.get_vreg_allocation(arg);
            if let Some(preg) = current_allocation.as_reg() {
                if regs.contains(preg) {
                    block_param_allocations[idx] = Allocation::reg(preg);
                    regs.remove(preg);
                    continue;
                }
            } else {
                block_param_allocations[idx] = current_allocation;
            }

            if let Some(preg) = regs.into_iter().next() {
                block_param_allocations[idx] = Allocation::reg(PReg::new(preg, arg.class()));
                regs.remove_idx(preg);
                continue;
            }

            if let Some(spillslot) = self.allocation_state.find_free_spillslot(class) {
                block_param_allocations[idx] = Allocation::stack(spillslot);
                continue;
            }

            block_param_allocations[idx] = Allocation::stack(self.allocation_state.allocate_spillslot(arg));
        }

        Ok(())
    }

    /// Free the specified preg, the value will be moved to a new allocation.
    /// other preg > spillslot
    #[inline]
    fn free_preg(&mut self, preg: PReg, blocked_pregs: HwRegSet) {
        let vreg = self.allocation_state.get_preg_vreg(preg).unwrap();
        let allocation = if let Some(preg) = self.allocation_state.find_free_preg(vreg.class(), blocked_pregs) {
            Allocation::reg(preg)
        } else {
            if let Some(spillslot) = self.allocation_state.find_free_spillslot(vreg.class()) {
                Allocation::stack(spillslot)
            } else {
                Allocation::stack(self.allocation_state.allocate_spillslot(vreg))
            }
        };

        self.allocation_state.free_allocation(vreg);
        self.edits.push((
            ProgPoint::new(self.current_inst, InstPosition::Before),
            Edit::Move {
                from: Allocation::reg(preg),
                to: allocation,
            },
        ));
        self.allocation_state.allocate_vreg(self.current_inst, vreg, allocation);
    }

    /// Allocate the operands of the current instruction.
    /// This function will generate the allocations, edits and update the state.
    #[inline]
    fn allocate_operands(&mut self) -> Result<(), RegAllocError> {
        let operands = self.func.inst_operands(self.current_inst);
        struct AllocationInstruction {
            /// Allocation of the operand.
            allocation_idx: usize,
            /// The operand to allocate.
            operand: Operand,
        }
        let mut allocation_instructions = SmallVec::<[AllocationInstruction; 8]>::from_iter(
            operands.iter().enumerate().map(|(idx, operand)| AllocationInstruction {
                allocation_idx: idx,
                operand: *operand,
            })
        );
        allocation_instructions.sort_unstable_by_key(|allocation_instruction| {
            match (allocation_instruction.operand.constraint(), allocation_instruction.operand.kind()) {
                (OperandConstraint::FixedReg(_), OperandKind::Def) => 0,
                (OperandConstraint::Reuse(idx), OperandKind::Def) => match operands[idx].constraint() {
                    OperandConstraint::FixedReg(_) => 1,
                    OperandConstraint::Reg => 2,
                    OperandConstraint::Any => 3,
                    OperandConstraint::Stack => 4,
                    _ => u8::MAX,
                },
                // Allocate stack operands before register operands, so regs may be freed.
                (OperandConstraint::Stack, OperandKind::Def) => 5,
                // We first allocate registers that are already allocated to a preg.
                (OperandConstraint::Reg, OperandKind::Def)
                if self.allocation_state.get_vreg_allocation(allocation_instruction.operand.vreg()).is_reg() => 6,
                (OperandConstraint::Reg, OperandKind::Def) => 7,
                (OperandConstraint::Any, OperandKind::Def) => 8,
                (OperandConstraint::FixedReg(_), OperandKind::Use) => 9,
                (OperandConstraint::Reg, OperandKind::Use) => 10,
                (OperandConstraint::Any, OperandKind::Use) => 11,
                (OperandConstraint::Stack, OperandKind::Use) => 12,
                _ => u8::MAX,
            }
        });

        let offset = self.inst_alloc_offsets[self.current_inst.index()] as usize;
        let mut fixed_regs_early = HwRegSet::empty();
        let mut fixed_regs_late = HwRegSet::empty();
        let (allocation_instructions_def, allocation_instructions_use) = {
            let allocation_instruction_pos = allocation_instructions.iter()
                .position(|allocation_instruction| allocation_instruction.operand.kind() == OperandKind::Use)
                .unwrap_or(allocation_instructions.len());
            allocation_instructions.split_at(allocation_instruction_pos)
        };
        for (allocation_instructions, stage) in [(allocation_instructions_def, OperandKind::Def), (allocation_instructions_use, OperandKind::Use)] {
            if stage == OperandKind::Use {
                // After the def stage we free all vregs of the def operands.
                for allocation_instruction in allocation_instructions_def {
                    let vreg = allocation_instruction.operand.vreg();
                    self.allocation_state.free_allocation(vreg);
                }
            }

            for allocation_instruction in allocation_instructions {
                let vreg = allocation_instruction.operand.vreg();
                let expected_allocation = self.allocation_state.get_vreg_allocation(vreg);
                let operand = allocation_instruction.operand;
                match (operand.constraint(), operand.kind()) {
                    (OperandConstraint::FixedReg(preg), OperandKind::Def) => {
                        // A fixed register is used as a def operand.
                        // IF the register is currently free we insert a move. (1 move)
                        // ELSE we spill the register content to another free preg first. (2 moves)
                        // ELSE we swap using a scratch register. (3 moves)
                        // ELSE we spill the register to a spillslot. (2 moves, but stack operation)
                        fixed_regs_late.add(preg);
                        if allocation_instruction.operand.pos() == OperandPos::Early {
                            fixed_regs_early.add(preg);
                        }

                        let definition_allocation = Allocation::reg(preg);
                        self.allocs[offset + allocation_instruction.allocation_idx] = definition_allocation;
                        if let Some(blocking_vreg) = self.allocation_state.get_preg_vreg(preg) {
                            // The preg is currently used by a vreg.
                            if let Some(free_preg) = self.allocation_state.find_free_preg(vreg.class(), HwRegSet::empty()) {
                                let free_allocation = Allocation::reg(free_preg);
                                // Edits in reverse order.
                                self.edits.push((
                                    ProgPoint::new(self.current_inst, InstPosition::After),
                                    Edit::Move {
                                        from: definition_allocation,
                                        to: expected_allocation,
                                    },
                                ));
                                self.edits.push((
                                    ProgPoint::new(self.current_inst, InstPosition::After),
                                    Edit::Move {
                                        from: free_allocation,
                                        to: definition_allocation,
                                    },
                                ));
                                // We free the old allocation.
                                self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                // We allocate the new allocation.
                                self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);
                                // We allocate the blocking vreg to the free preg.
                                self.allocation_state.allocate_vreg(self.current_inst, blocking_vreg, free_allocation);
                            } else {
                                if let Some(scratch_preg) = self.allocation_state.find_scratch_reg(vreg.class(), HwRegSet::empty()) {
                                    let scratch_allocation = Allocation::reg(scratch_preg);
                                    // Edits in reverse order.
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: scratch_allocation,
                                            to: expected_allocation,
                                        },
                                    ));
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: expected_allocation,
                                            to: definition_allocation,
                                        },
                                    ));
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: definition_allocation,
                                            to: scratch_allocation,
                                        },
                                    ));
                                    // We allocate the new allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);
                                    // We allocate the blocking vreg to the original preg.
                                    self.allocation_state.allocate_vreg(self.current_inst, blocking_vreg, expected_allocation);
                                } else {
                                    let spillslot = self.allocation_state.allocate_spillslot(blocking_vreg);
                                    let spill_allocation = Allocation::stack(spillslot);
                                    // Edits in reverse order.
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: spill_allocation,
                                            to: definition_allocation,
                                        },
                                    ));
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: definition_allocation,
                                            to: expected_allocation,
                                        },
                                    ));
                                    // We free the old allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                    // We allocate the new allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);
                                    // We allocate the blocking vreg to the spillslot.
                                    self.allocation_state.allocate_vreg(self.current_inst, blocking_vreg, spill_allocation);
                                }
                            }
                        } else {
                            // The preg is currently free.
                            self.edits.push((
                                ProgPoint::new(self.current_inst, InstPosition::After),
                                Edit::Move {
                                    from: definition_allocation,
                                    to: expected_allocation,
                                },
                            ));
                            // We free the old allocation.
                            self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                            // We allocate the new allocation.
                            self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);
                        }
                    }
                    (OperandConstraint::Reg, OperandKind::Def) => {
                        let vreg = operand.vreg();
                        let current_allocation = self.allocation_state.get_vreg_allocation(vreg);
                        let mut blocked_pregs = fixed_regs_late;
                        if allocation_instruction.operand.pos() == OperandPos::Early {
                            blocked_pregs = blocked_pregs | fixed_regs_early;
                        }
                        let preg = match current_allocation.as_reg() {
                            Some(preg) if !blocked_pregs.contains(preg) => {
                                // The vreg is already allocated to an unblocked preg.
                                // We can just use it.
                                preg
                            }
                            _ => {
                                // Find a free preg.
                                if let Some(preg) = self.allocation_state.find_free_preg(vreg.class(), blocked_pregs) {
                                    // Move from this preg
                                    let definition_allocation = Allocation::reg(preg);
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: definition_allocation,
                                            to: expected_allocation,
                                        },
                                    ));
                                    // We free the old allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                    // We allocate the new allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);

                                    preg
                                } else {
                                    // Find a used preg.
                                    let preg = self.allocation_state.find_furthest_used_preg(vreg.class(), blocked_pregs)
                                        .ok_or(RegAllocError::TooManyLiveRegs)?;
                                    let blocking_vreg = self.allocation_state.get_preg_vreg(preg).unwrap();
                                    let definition_allocation = Allocation::reg(preg);
                                    if let Some(scratch_preg) = self.allocation_state.find_scratch_reg(vreg.class(), HwRegSet::empty()) {
                                        let scratch_allocation = Allocation::reg(scratch_preg);
                                        // Edits in reverse order.
                                        self.edits.push((
                                            ProgPoint::new(self.current_inst, InstPosition::After),
                                            Edit::Move {
                                                from: scratch_allocation,
                                                to: expected_allocation,
                                            },
                                        ));
                                        self.edits.push((
                                            ProgPoint::new(self.current_inst, InstPosition::After),
                                            Edit::Move {
                                                from: expected_allocation,
                                                to: definition_allocation,
                                            },
                                        ));
                                        self.edits.push((
                                            ProgPoint::new(self.current_inst, InstPosition::After),
                                            Edit::Move {
                                                from: definition_allocation,
                                                to: scratch_allocation,
                                            },
                                        ));
                                        // We allocate the new allocation.
                                        self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);
                                        // We allocate the blocking vreg to the original preg.
                                        self.allocation_state.allocate_vreg(self.current_inst, blocking_vreg, expected_allocation);
                                    } else {
                                        let spillslot = self.allocation_state.allocate_spillslot(blocking_vreg);
                                        let spill_allocation = Allocation::stack(spillslot);
                                        // Edits in reverse order.
                                        self.edits.push((
                                            ProgPoint::new(self.current_inst, InstPosition::After),
                                            Edit::Move {
                                                from: spill_allocation,
                                                to: definition_allocation,
                                            },
                                        ));
                                        self.edits.push((
                                            ProgPoint::new(self.current_inst, InstPosition::After),
                                            Edit::Move {
                                                from: definition_allocation,
                                                to: expected_allocation,
                                            },
                                        ));
                                        // We free the old allocation.
                                        self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                        // We allocate the new allocation.
                                        self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);
                                        // We allocate the blocking vreg to the spillslot.
                                        self.allocation_state.allocate_vreg(self.current_inst, blocking_vreg, spill_allocation);
                                    }

                                    preg
                                }
                            }
                        };
                        let definition_allocation = Allocation::reg(preg);
                        self.allocs[offset + allocation_instruction.allocation_idx] = definition_allocation;

                        fixed_regs_late.add(preg);
                        if allocation_instruction.operand.pos() == OperandPos::Early {
                            fixed_regs_early.add(preg);
                        }

                    }
                    (OperandConstraint::Any, OperandKind::Def) => {
                        let vreg = operand.vreg();
                        let current_allocation = self.allocation_state.get_vreg_allocation(vreg);
                        let mut blocked_pregs = fixed_regs_late;
                        if allocation_instruction.operand.pos() == OperandPos::Early {
                            blocked_pregs = blocked_pregs | fixed_regs_early;
                        }
                        let definition_allocation = match current_allocation.as_reg() {
                            Some(preg) if !blocked_pregs.contains(preg) => {
                                // The vreg is already allocated to an unblocked preg.
                                // We can just use it.
                                Allocation::reg(preg)
                            }
                            Some(_) => {
                                // The vreg is already allocated to a blocked preg.
                                if let Some(preg) = self.allocation_state.find_free_preg(vreg.class(), blocked_pregs) {
                                    // There is an unblocked preg we can use.
                                    // Move from this preg
                                    let definition_allocation = Allocation::reg(preg);
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: definition_allocation,
                                            to: expected_allocation,
                                        },
                                    ));
                                    // We free the old allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                    // We allocate the new allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);

                                    definition_allocation
                                } else {
                                    // Just use a spillslot.
                                    let spillslot = self.allocation_state.allocate_spillslot(vreg);
                                    let spill_allocation = Allocation::stack(spillslot);
                                    // Edits in reverse order.
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: spill_allocation,
                                            to: expected_allocation,
                                        },
                                    ));
                                    // We free the old allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                    // We allocate the new allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, vreg, spill_allocation);

                                    spill_allocation
                                }
                            }
                            None => {
                                current_allocation
                            }
                        };

                        self.allocs[offset + allocation_instruction.allocation_idx] = definition_allocation;
                        if let Some(preg) = definition_allocation.as_reg() {
                            fixed_regs_late.add(preg);
                            if allocation_instruction.operand.pos() == OperandPos::Early {
                                fixed_regs_early.add(preg);
                            }
                        }
                    }
                    (OperandConstraint::Stack, OperandKind::Def) => {
                        let vreg = operand.vreg();
                        let current_allocation = self.allocation_state.get_vreg_allocation(vreg);
                        let definition_allocation = match current_allocation.as_stack() {
                            Some(spillslot) => {
                                // The vreg is already allocated to a spillslot.
                                // We can just use it.
                                Allocation::stack(spillslot)
                            }
                            _ => {
                                // Just use a spillslot.
                                let spillslot = self.allocation_state.allocate_spillslot(vreg);
                                let definition_allocation = Allocation::stack(spillslot);
                                // Edits in reverse order.
                                self.edits.push((
                                    ProgPoint::new(self.current_inst, InstPosition::After),
                                    Edit::Move {
                                        from: definition_allocation,
                                        to: expected_allocation,
                                    },
                                ));
                                // We free the old allocation.
                                self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                // We allocate the new allocation.
                                self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);

                                definition_allocation
                            }
                        };

                        self.allocs[offset + allocation_instruction.allocation_idx] = definition_allocation;
                    }
                    (OperandConstraint::Reuse(idx), OperandKind::Def) => {
                        // This constraint is the most difficult to handle.
                        // We find an allocation satisfying the constraint this operand is reusing.
                        let vreg = operand.vreg();
                        let allocation = self.allocation_state.get_vreg_allocation(vreg);
                        let reused_operand = operands[idx];
                        let reused_allocation = match reused_operand.constraint() {
                            OperandConstraint::Any => allocation,
                            OperandConstraint::Reg => {
                                let blocked_pregs = fixed_regs_early | fixed_regs_late;
                                match allocation.as_reg() {
                                    Some(preg) if !blocked_pregs.contains(preg) => allocation,
                                    _ => {
                                        // The vreg is already allocated to a blocked preg.
                                        if let Some(preg) = self.allocation_state.find_free_preg(vreg.class(), blocked_pregs) {
                                            // There is an unblocked preg we can use.
                                            // Move from this preg
                                            let definition_allocation = Allocation::reg(preg);
                                            self.edits.push((
                                                ProgPoint::new(self.current_inst, InstPosition::After),
                                                Edit::Move {
                                                    from: definition_allocation,
                                                    to: expected_allocation,
                                                },
                                            ));
                                            // We free the old allocation.
                                            self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                            // We allocate the new allocation.
                                            self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);

                                            definition_allocation
                                        } else {
                                            // Find a used preg.
                                            let preg = self.allocation_state.find_furthest_used_preg(vreg.class(), blocked_pregs)
                                                .ok_or(RegAllocError::TooManyLiveRegs)?;
                                            let blocking_vreg = self.allocation_state.get_preg_vreg(preg).unwrap();
                                            let definition_allocation = Allocation::reg(preg);
                                            if let Some(scratch_preg) = self.allocation_state.find_scratch_reg(vreg.class(), HwRegSet::empty()) {
                                                let scratch_allocation = Allocation::reg(scratch_preg);
                                                // Edits in reverse order.
                                                self.edits.push((
                                                    ProgPoint::new(self.current_inst, InstPosition::After),
                                                    Edit::Move {
                                                        from: scratch_allocation,
                                                        to: expected_allocation,
                                                    },
                                                ));
                                                self.edits.push((
                                                    ProgPoint::new(self.current_inst, InstPosition::After),
                                                    Edit::Move {
                                                        from: expected_allocation,
                                                        to: definition_allocation,
                                                    },
                                                ));
                                                self.edits.push((
                                                    ProgPoint::new(self.current_inst, InstPosition::After),
                                                    Edit::Move {
                                                        from: definition_allocation,
                                                        to: scratch_allocation,
                                                    },
                                                ));
                                                // We allocate the new allocation.
                                                self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);
                                                // We allocate the blocking vreg to the original preg.
                                                self.allocation_state.allocate_vreg(self.current_inst, blocking_vreg, expected_allocation);
                                            } else {
                                                let spillslot = self.allocation_state.allocate_spillslot(blocking_vreg);
                                                let spill_allocation = Allocation::stack(spillslot);
                                                // Edits in reverse order.
                                                self.edits.push((
                                                    ProgPoint::new(self.current_inst, InstPosition::After),
                                                    Edit::Move {
                                                        from: spill_allocation,
                                                        to: definition_allocation,
                                                    },
                                                ));
                                                self.edits.push((
                                                    ProgPoint::new(self.current_inst, InstPosition::After),
                                                    Edit::Move {
                                                        from: definition_allocation,
                                                        to: expected_allocation,
                                                    },
                                                ));
                                                // We free the old allocation.
                                                self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                                // We allocate the new allocation.
                                                self.allocation_state.allocate_vreg(self.current_inst, vreg, definition_allocation);
                                                // We allocate the blocking vreg to the spillslot.
                                                self.allocation_state.allocate_vreg(self.current_inst, blocking_vreg, spill_allocation);
                                            }

                                            definition_allocation
                                        }
                                    }
                                }
                            }
                            OperandConstraint::Stack => {
                                if let Some(_) = allocation.as_stack() {
                                    allocation
                                } else {
                                    let spillslot = self.allocation_state.allocate_spillslot(vreg);
                                    let spill_allocation = Allocation::stack(spillslot);
                                    // Edits in reverse order.
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::Before),
                                        Edit::Move {
                                            from: spill_allocation,
                                            to: expected_allocation,
                                        },
                                    ));
                                    // We free the old allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, VReg::invalid(), expected_allocation);
                                    // We allocate the new allocation.
                                    self.allocation_state.allocate_vreg(self.current_inst, vreg, spill_allocation);

                                    spill_allocation
                                }
                            }
                            OperandConstraint::FixedReg(preg) => Allocation::reg(preg),
                            OperandConstraint::Reuse(_) => return Err(RegAllocError::SSA(vreg, self.current_inst)),
                        };
                        self.allocs[offset + allocation_instruction.allocation_idx] = reused_allocation;
                        self.allocs[offset + idx] = reused_allocation;
                    }
                    (OperandConstraint::FixedReg(preg), OperandKind::Use) => {
                        let allocation = if self.allocs[offset + allocation_instruction.allocation_idx].is_some() {
                            self.allocs[offset + allocation_instruction.allocation_idx]
                        } else {
                            Allocation::reg(preg)
                        };
                        self.allocs[offset + allocation_instruction.allocation_idx] = allocation;
                        fixed_regs_early.add(preg);
                        self.allocation_state.allocate_vreg(self.current_inst, operand.vreg(), allocation);
                    },
                    (OperandConstraint::Reg, OperandKind::Use) => {
                        let allocation = if self.allocs[offset + allocation_instruction.allocation_idx].is_some() {
                            self.allocs[offset + allocation_instruction.allocation_idx]
                        } else {
                            let late_blocked_early_free = !fixed_regs_early & fixed_regs_late;
                            if let Some(preg) = self.allocation_state.find_free_preg(operand.class(), !late_blocked_early_free) {
                                fixed_regs_early.add(preg);
                                Allocation::reg(preg)
                            } else {
                                if let Some(preg) = self.allocation_state.find_free_preg(operand.class(), fixed_regs_early) {
                                    fixed_regs_early.add(preg);
                                    Allocation::reg(preg)
                                } else {
                                    let preg = self.allocation_state.find_furthest_used_preg(operand.class(), fixed_regs_early)
                                        .ok_or(RegAllocError::TooManyLiveRegs)?;
                                    fixed_regs_early.add(preg);
                                    let allocation = Allocation::reg(preg);
                                    let vreg = self.allocation_state.get_preg_vreg(preg).unwrap();
                                    let spillslot = self.allocation_state.allocate_spillslot(vreg);
                                    // Edits in reverse order.
                                    self.edits.push((
                                        ProgPoint::new(self.current_inst, InstPosition::After),
                                        Edit::Move {
                                            from: Allocation::stack(spillslot),
                                            to: allocation,
                                        },
                                    ));

                                    self.allocation_state.allocate_vreg(self.current_inst, vreg, Allocation::stack(spillslot));

                                    allocation
                                }
                            }

                        };
                        self.allocs[offset + allocation_instruction.allocation_idx] = allocation;
                        self.allocation_state.allocate_vreg(self.current_inst, operand.vreg(), allocation);
                    },
                    (OperandConstraint::Any, OperandKind::Use) => {
                        let allocation = if self.allocs[offset + allocation_instruction.allocation_idx].is_some() {
                            self.allocs[offset + allocation_instruction.allocation_idx]
                        } else {
                            let late_blocked_early_free = !fixed_regs_early & fixed_regs_late;
                            if let Some(preg) = self.allocation_state.find_free_preg(operand.class(), !late_blocked_early_free) {
                                fixed_regs_early.add(preg);
                                Allocation::reg(preg)
                            } else {
                                if let Some(preg) = self.allocation_state.find_free_preg(operand.class(), fixed_regs_early) {
                                    fixed_regs_early.add(preg);
                                    Allocation::reg(preg)
                                } else {
                                    // Just use a spillslot.
                                    Allocation::stack(self.allocation_state.allocate_spillslot(operand.vreg()))
                                }
                            }
                        };
                        self.allocs[offset + allocation_instruction.allocation_idx] = allocation;
                        self.allocation_state.allocate_vreg(self.current_inst, operand.vreg(), allocation);
                    },
                    (OperandConstraint::Stack, OperandKind::Use) => {
                        let allocation = if self.allocs[offset + allocation_instruction.allocation_idx].is_some() {
                            self.allocs[offset + allocation_instruction.allocation_idx]
                        } else {
                            Allocation::stack(self.allocation_state.allocate_spillslot(operand.vreg()))
                        };
                        self.allocs[offset + allocation_instruction.allocation_idx] = allocation;
                        self.allocation_state.allocate_vreg(self.current_inst, operand.vreg(), allocation);
                    },
                    _ => return Err(RegAllocError::SSA(vreg, self.current_inst)),
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::println;

    use crate::fuzzing::arbitrary::{Arbitrary, Unstructured};
    use crate::fuzzing::func::{Func, machine_env, Options};

    #[test]
    fn test() {
        println!("test");
        let mut unstructured = Unstructured::new(&[4, 5, 6, 7, 6]);
        let env = machine_env();
        let func = Func::arbitrary_with_options(&mut unstructured, &Options {
            reused_inputs: true,
            fixed_regs: true,
            fixed_nonallocatable: true,
            clobbers: false,
            reftypes: false,
        }).unwrap();
        println!("{:?}", &func);
        let allocator = super::Env::new(&func, &env);
        let result = allocator.run().unwrap();
        println!("{:?}", result);
    }
}