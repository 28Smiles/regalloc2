use std::vec::Vec;
use smallvec::SmallVec;

use crate::{Allocation, Block, Edit, Function, Inst, InstPosition, InstRange, MachineEnv, Operand, OperandConstraint, OperandKind, OperandPos, PReg, PRegSet, ProgPoint, RegAllocError, RegClass, SpillSlot, VReg};

mod usage_tracker;
mod allocation_tracker;

#[derive(Copy, Clone, Debug)]
struct PRegAlloc {
    vreg: VReg,
    last_use: Inst,
}

struct Env<'a, F: Function> {
    func: &'a F,
    mach_env: &'a MachineEnv,

    num_spillslots: u32,
    edits: Vec<(ProgPoint, Edit)>,
    // Spill slots
    free_spillslots_per_class: [Vec<SpillSlot>; 3],
    spillslot_allocations: Vec<VReg>,
    // Allocations
    inst_alloc_offsets: Vec<u32>,
    allocs: Vec<Allocation>,
    // Blockparams
    block_params_offsets: Vec<usize>,
    block_params: Vec<Allocation>,
    // State
    current_block: Block,
    current_block_inst_range: InstRange,
    current_inst: Inst,
    // PRegs
    allocated_pregs: PRegSet,
    preg_allocations: Vec<PRegAlloc>,
    // VRegs
    vreg_allocations: Vec<Allocation>,
    vregs_in_use: Vec<VReg>,
    // Live ranges
    vreg_live_ranges: Vec<InstRange>,
}

impl<'a, F: Function> Env<'a, F> {
    #[inline]
    fn to(mut self, block: Block, params: &[Allocation]) -> Self {
        self.current_block = block;
        self.current_block_inst_range = self.func.block_insts(block);
        self.current_inst = self.current_block_inst_range.first();
        // Reset the PRegs
        self.allocated_pregs = PRegSet::empty();
        // Reset the spill slots
        for &vreg in &self.vregs_in_use {
            let alloc = self.vreg_allocations[vreg.vreg()];
            if let Some(spillslot) = alloc.as_stack() {
                self.free_spillslots_per_class[vreg.class() as usize].push(spillslot);
            }
            self.vreg_allocations[vreg.vreg()] = Allocation::none();
            self.vreg_live_ranges[vreg.vreg()] = InstRange::new(
                self.current_block_inst_range.last(),
                self.current_block_inst_range.first(),
            );
        }
        self.vregs_in_use.clear();
        // Set the blockparams
        for (&vreg, &alloc) in self.func.block_params(block).iter().zip(params) {
            self.vreg_allocations[vreg.vreg()] = alloc;
            self.vregs_in_use.push(vreg);
            if let Some(spillslot) = alloc.as_stack() {
                self.free_spillslots_per_class[vreg.class() as usize].retain(|&s| s != spillslot);
            }
            if let Some(preg) = alloc.as_reg() {
                self.allocated_pregs.insert(preg);
                self.preg_allocations[preg.index()].vreg = vreg;
                self.preg_allocations[preg.index()].last_use = self.current_inst;
            }
        }
        // Discover the live ranges
        for inst in self.current_block_inst_range.iter() {
            for operand in self.func.inst_operands(inst) {
                let vreg = operand.vreg();
                let InstRange(start, end) = self.vreg_live_ranges[vreg.vreg()];
                self.vreg_live_ranges[vreg.vreg()] = InstRange(start.min(inst), end.max(inst));
            }
        }

        self
    }

    /// Allocate the block parameters. (Will only work on branch instructions)
    #[inline]
    fn allocate_args(&mut self) -> Result<(), RegAllocError> {
        if !self.func.is_branch(self.current_inst) {
            return Ok(());
        }

        for (idx, &target_block) in self.func.block_succs(self.current_block).iter().enumerate() {
            let block_params = self.block_param_allocations(target_block);
            let vreg_source = self.func.branch_blockparams(target_block, self.current_inst, idx);
            let vreg_dest = self.func.block_params(target_block);

            for (&source_vreg, (&dest_vreg, &dest_allocation)) in vreg_source.iter().zip(vreg_dest.iter().zip(block_params)) {
                let source_allocation = self.vreg_allocations[source_vreg.vreg()];
                if dest_allocation != source_allocation {
                    self.edits.push((
                        ProgPoint::new(self.current_inst, InstPosition::Before),
                        Edit::Move {
                            from: source_allocation,
                            to: dest_allocation,
                        },
                    ));
                    self.vreg_allocations[dest_vreg.vreg()] = dest_allocation;
                    self.vregs_in_use.push(dest_vreg);
                }
            }
        }

        Ok(())
    }

    #[inline]
    fn block_param_allocations(&self, block: Block) -> &[Allocation] {
        let index = block.index();
        debug_assert!(index < self.block_params_offsets.len() - 1);
        let start = self.block_params_offsets[index];
        let end = self.block_params_offsets.get(index + 1).copied().unwrap_or(self.block_params.len());

        &self.block_params[start..end]
    }

    /// Allocate the operands of the current instruction.
    /// This function will generate the allocations, edits and update the state.
    #[inline]
    fn allocate_operands(&mut self) -> Result<(), RegAllocError> {
        enum AllocationStep {
            /// Use this allocation. The operand is already allocated correctly.
            Use,
            /// Move the value from the old allocation to the new allocation.
            Move,
            /// Swap the values of the old and new allocations.
            Swap,
            /// Spill the old allocation to a stack slot.
            Spill,
            /// Copy the value from the old allocation to the new allocation.
            /// The old allocation is still live after this instruction.
            Copy,
        }

        struct AllocationInstruction {
            /// Allocation of the operand.
            allocation: Allocation,
            /// The operand to allocate.
            operand: Operand,
            /// The allocation step to take.
            step: AllocationStep,
        }

        let mut allocation_instructions = SmallVec::<[(AllocationInstruction, usize); 4]>::new();
        allocation_instructions.extend(self.func.inst_operands(self.current_inst).iter()
            .map(|operand| AllocationInstruction {
                allocation: Allocation::none(),
                operand: *operand,
                step: AllocationStep::Use,
            }).enumerate());
        // Sort by strictness of the constraint.
        allocation_instructions.sort_unstable_by_key(|(allocation, _)| {
            match (allocation.operand.constraint(), allocation.operand.kind()) {
                // Fixed registers are the most strict.
                (OperandConstraint::FixedReg(_), _) => 0,
                // Next are the uses, since we want to reuse the reg if possible/needed.
                // We start with the reg constraints.
                (OperandConstraint::Reg, OperandKind::Use) => 1,
                // Then any constraints (we try to move into a preg, if not just use).
                (OperandConstraint::Any, OperandKind::Use) => 2,
                // Then the stack constraints (we just use the current allocation or spill).
                (OperandConstraint::Stack, OperandKind::Use) => 3,
                // Then the def constraints.
                // We start by the reuse constraints
                (OperandConstraint::Reuse(_), _) => 4,
                // Then the reg constraints.
                (OperandConstraint::Reg, OperandKind::Def) => 5,
                // Then any constraints (we prefer pregs if possible).
                (OperandConstraint::Any, OperandKind::Def) => 6,
                // Then the stack constraints (we just reuse or spill).
                (OperandConstraint::Stack, OperandKind::Def) => 7,
            }
        });

        let mut allocation_instruction_pointer = SmallVec::<[usize; 4]>::from_elem(0, allocation_instructions.len());
        for (instruction_index, (_, allocation_index)) in allocation_instructions.iter().enumerate() {
            allocation_instruction_pointer[*allocation_index] = instruction_index;
        }
        let mut early_blocked_pregs = PRegSet::empty();
        let mut late_blocked_pregs = PRegSet::empty();

        for allocation_instruction_idx in 0..allocation_instructions.len() {
            let (
                allocated_allocation_instructions,
                [(allocation_instruction, allocation_index), ..]
            ) = allocation_instructions.split_at_mut(allocation_instruction_idx);
            let allocation_index = *allocation_index;
            let vreg = allocation_instruction.operand.vreg();

            // Update blocked pregs.
            if let Some((last_allocation, _)) = allocated_allocation_instructions.last_mut() {
                if let Some(preg) = last_allocation.allocation.as_reg() {
                    match last_allocation.operand.kind() {
                        OperandKind::Def => {
                            if allocation_instruction.operand.pos() != OperandPos::Early {
                                early_blocked_pregs.add(preg);
                            }
                            late_blocked_pregs.add(preg);
                        }
                        OperandKind::Use => {
                            // If the vreg is not live after this instruction, we can reuse the allocation later.
                            let InstRange(_, last_use) = self.vreg_live_ranges[vreg.vreg()];
                            let not_live = last_use <= self.current_inst;
                            let not_late = allocation_instruction.operand.pos() != OperandPos::Late;
                            let may_reuse = not_live && not_late;
                            early_blocked_pregs.add(preg);
                            if !may_reuse {
                                late_blocked_pregs.add(preg);
                            }
                        }
                    }
                }

            }

            // Try to allocate the operand.
            match allocation_instruction.operand.constraint() {
                OperandConstraint::Any => {
                    let current_allocation = self.get_vreg_allocation(vreg);
                    match allocation_instruction.operand.kind() {
                        OperandKind::Def => {
                            debug_assert!(current_allocation.is_none());
                            match allocation_instruction.operand.pos() {
                                OperandPos::Early => {
                                    // If there is a free preg, use it.
                                    if let Some(preg) = self.find_free_preg(vreg.class(), early_blocked_pregs | self.allocated_pregs) {
                                        allocation_instruction.allocation = Allocation::reg(preg);
                                        allocation_instruction.step = AllocationStep::Use;
                                        continue;
                                    }
                                }
                                OperandPos::Late => {
                                    // If there is a free preg, use it.
                                    if let Some(preg) = self.find_free_preg(vreg.class(), late_blocked_pregs | self.allocated_pregs) {
                                        allocation_instruction.allocation = Allocation::reg(preg);
                                        allocation_instruction.step = AllocationStep::Use;
                                        continue;
                                    }
                                }
                            }
                            // Spill the vreg to a stack slot.
                            allocation_instruction.allocation = Allocation::stack(self.allocate_spillslot(vreg));
                            allocation_instruction.step = AllocationStep::Use;
                        }
                        OperandKind::Use => {
                            // If there is a free preg, use it.
                            let mut early_blocked_pregs = early_blocked_pregs;
                            early_blocked_pregs.union_from(self.allocated_pregs);
                            if let Some(preg) = self.find_free_preg(vreg.class(), early_blocked_pregs) {
                                allocation_instruction.allocation = Allocation::reg(preg);
                                allocation_instruction.step = AllocationStep::Move;

                                continue;
                            }
                            // If there is a freeable preg, use it.
                            if let Some(preg) = self.find_freeable_preg(vreg, early_blocked_pregs).ok() {
                                let preg_allocation = self.preg_allocations[preg.index()].vreg;
                                allocation_instruction.allocation = Allocation::reg(preg);
                                if preg_allocation.class() == vreg.class() {
                                    allocation_instruction.step = AllocationStep::Swap;
                                } else {
                                    allocation_instruction.step = AllocationStep::Spill;
                                }
                                continue;
                            }
                            let current_allocation = current_allocation.unwrap();
                            allocation_instruction.allocation = current_allocation;
                            allocation_instruction.step = AllocationStep::Use;
                        }
                    }
                }
                OperandConstraint::Reg => {
                    let current_allocation = self.get_vreg_allocation(vreg);
                    match allocation_instruction.operand.kind() {
                        OperandKind::Def => {
                            debug_assert!(current_allocation.is_none());
                            match allocation_instruction.operand.pos() {
                                OperandPos::Early => {
                                    // If there is a free preg, use it.
                                    if let Some(preg) = self.find_free_preg(vreg.class(), early_blocked_pregs | self.allocated_pregs) {
                                        allocation_instruction.allocation = Allocation::reg(preg);
                                        allocation_instruction.step = AllocationStep::Use;
                                        continue;
                                    }
                                    // If there is a freeable preg, use it.
                                    let preg = self.find_freeable_preg(vreg, early_blocked_pregs)?;
                                    allocation_instruction.allocation = Allocation::reg(preg);
                                    allocation_instruction.step = AllocationStep::Spill;
                                }
                                OperandPos::Late => {
                                    // We attempt to reuse first.
                                    // Reuse registers are those who blocked in the early position
                                    // and are not blocked in the late position.
                                    let reuse_pregs = !(early_blocked_pregs & !late_blocked_pregs);
                                    if let Some(preg) = self.find_free_preg(vreg.class(), reuse_pregs) {
                                        allocation_instruction.allocation = Allocation::reg(preg);
                                        allocation_instruction.step = AllocationStep::Use;
                                        continue;
                                    }
                                    // If there is a free preg, use it.
                                    if let Some(preg) = self.find_free_preg(vreg.class(), late_blocked_pregs | self.allocated_pregs) {
                                        allocation_instruction.allocation = Allocation::reg(preg);
                                        allocation_instruction.step = AllocationStep::Use;
                                        continue;
                                    }
                                    // If there is a freeable preg, use it.
                                    if let Some(preg) = self.find_freeable_preg(vreg, late_blocked_pregs).ok() {
                                        allocation_instruction.allocation = Allocation::reg(preg);
                                        allocation_instruction.step = AllocationStep::Spill;
                                        continue;
                                    }
                                    todo!("OperandConstraint::Reg::Def::Late")
                                }
                            }
                        }
                        OperandKind::Use => {
                            let current_allocation = current_allocation.unwrap();
                            // If the vreg is already allocated correctly, just use it.
                            if let Some(_) = current_allocation.as_reg() {
                                allocation_instruction.allocation = current_allocation;
                                allocation_instruction.step = AllocationStep::Use;
                                continue;
                            }
                            // If there is a free preg, use it.
                            if let Some(preg) = self.find_free_preg(vreg.class(), early_blocked_pregs | self.allocated_pregs) {
                                allocation_instruction.allocation = Allocation::reg(preg);
                                allocation_instruction.step = AllocationStep::Move;
                                continue;
                            }
                            // If there is a freeable preg, use it.
                            let preg = self.find_freeable_preg(vreg, early_blocked_pregs | self.allocated_pregs)?;
                            let preg_allocation = self.preg_allocations[preg.index()].vreg;
                            allocation_instruction.allocation = Allocation::reg(preg);
                            if preg_allocation.class() == vreg.class() {
                                allocation_instruction.step = AllocationStep::Swap;
                            } else {
                                allocation_instruction.step = AllocationStep::Spill;
                            }
                        }
                    }
                }
                OperandConstraint::Stack => {
                    let current_allocation = self.get_vreg_allocation(vreg);
                    match allocation_instruction.operand.kind() {
                        OperandKind::Def => {
                            debug_assert!(current_allocation.is_none());
                            allocation_instruction.allocation = Allocation::stack(self.allocate_spillslot(vreg));
                            allocation_instruction.step = AllocationStep::Move;
                        }
                        OperandKind::Use => {
                            let current_allocation = current_allocation.unwrap();
                            if let Some(_) = current_allocation.as_stack() {
                                allocation_instruction.allocation = current_allocation;
                                allocation_instruction.step = AllocationStep::Use;
                            }
                            allocation_instruction.allocation = Allocation::stack(self.allocate_spillslot(vreg));
                            allocation_instruction.step = AllocationStep::Move;
                        }
                    }
                }
                OperandConstraint::FixedReg(preg) => {
                    early_blocked_pregs.insert(preg);
                    if allocation_instruction.operand.pos() == OperandPos::Late {
                        late_blocked_pregs.insert(preg);
                    }
                    allocation_instruction.allocation = Allocation::reg(preg);
                    allocation_instruction.step = AllocationStep::Use;
                }
                OperandConstraint::Reuse(idx) => {
                    let pointer = allocation_instruction_pointer[idx]; // The index of the allocation instruction.
                    debug_assert!(pointer < allocation_instruction_idx); // The allocation instruction must be before this one.
                    let (allocated_allocation_instruction, _) = &mut allocated_allocation_instructions[pointer];
                    allocation_instruction.allocation = allocated_allocation_instruction.allocation;
                    if let Some(preg) = allocation_instruction.allocation.as_reg() {
                        late_blocked_pregs.add(preg);
                    }
                }
            }
        }

        // Now all the operands are allocated, we can generate the edits and update the state.
        let allocation_offset = self.inst_alloc_offsets[self.current_inst.index()];
        for (allocation_instruction, allocation_idx) in allocation_instructions {
            // Set the operand allocation.
            self.allocs[allocation_offset + allocation_idx] = allocation_instruction.allocation;
            // Generate the edit.
            match allocation_instruction.step {
                AllocationStep::Use => {
                    match allocation_instruction.operand.kind() {
                        OperandKind::Def => {
                            let vreg = allocation_instruction.operand.vreg();
                            self.vregs_in_use.push(vreg);
                            self.free_allocation_state(allocation_instruction.allocation);
                            self.set_allocation_state(vreg, allocation_instruction.allocation);
                        }
                        OperandKind::Use => {
                            let vreg = allocation_instruction.operand.vreg();
                            let InstRange(_, end) = self.vreg_live_ranges[vreg.vreg()];
                            if end == self.current_inst {
                                // We free if the vreg is not live after this instruction (last use).
                                self.free_allocation_state(allocation_instruction.allocation);
                            }
                            if let Some(preg) = allocation_instruction.allocation.as_reg() {
                                self.preg_allocations[preg.index()].last_use = self.current_inst;
                            }
                        }
                    }
                }
                AllocationStep::Move => {
                    debug_assert!(allocation_instruction.operand.kind() == OperandKind::Use);
                    debug_assert!(allocation_instruction.operand.vreg() != VReg::invalid());
                    let old_allocation = self.vreg_allocations[allocation_instruction.operand.vreg().vreg()];
                    let new_allocation = allocation_instruction.allocation;
                    debug_assert!(old_allocation != new_allocation);
                    self.edits.push((
                        ProgPoint::new(self.current_inst, InstPosition::Before),
                        Edit::Move {
                            from: old_allocation,
                            to: new_allocation,
                        },
                    ));
                    // Update the state.
                    let vreg = allocation_instruction.operand.vreg();
                    self.free_allocation_state(old_allocation);
                    self.free_allocation_state(new_allocation);
                    self.set_allocation_state(vreg, new_allocation);
                }
                AllocationStep::Swap => {
                    debug_assert!(allocation_instruction.operand.vreg() != VReg::invalid());
                    let allocation1 = allocation_instruction.allocation;
                    let allocation2 = self.vreg_allocations[allocation_instruction.operand.vreg().vreg()];
                    let vreg1 = allocation_instruction.operand.vreg();
                    let vreg2 = self.get_allocation_vreg(allocation2).unwrap();
                    debug_assert!(allocation1 != allocation2);
                    debug_assert!(vreg1 != vreg2);
                    debug_assert!(allocation1.is_reg());
                    debug_assert!(allocation2.is_reg());
                    if let Some(scratch_reg) = self.find_scratch_reg(
                        early_blocked_pregs | self.allocated_pregs,
                        allocation1.reg_class(),
                    ) {
                        // We need to generate 3 moves using a scratch register.
                        let scratch_allocation = Allocation::reg(scratch_reg);
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: allocation1,
                                to: scratch_allocation,
                            },
                        ));
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: allocation2,
                                to: allocation1,
                            },
                        ));
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: scratch_allocation,
                                to: allocation2,
                            },
                        ));
                    } else {
                        // Just spill one of the allocations to a stack slot.
                        let spillslot = Allocation::stack(self.allocate_spillslot(vreg1));
                        self.set_allocation_state(vreg1, spillslot);
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: allocation1,
                                to: spillslot,
                            },
                        ));
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: allocation2,
                                to: allocation1,
                            },
                        ));
                        self.edits.push((
                            ProgPoint::new(self.current_inst, InstPosition::Before),
                            Edit::Move {
                                from: spillslot,
                                to: allocation2,
                            },
                        ));
                        self.free_allocation_state(spillslot);
                    }
                    self.set_allocation_state(vreg1, allocation2);
                    self.set_allocation_state(vreg2, allocation1);
                }
                AllocationStep::Spill => {
                    let vreg = allocation_instruction.operand.vreg();
                    let allocation = allocation_instruction.allocation;
                    debug_assert!(allocation.is_reg());
                    let old_vreg = self.get_allocation_vreg(allocation).unwrap();
                    let spillslot = Allocation::stack(self.allocate_spillslot(vreg));
                    self.edits.push((
                        ProgPoint::new(self.current_inst, InstPosition::Before),
                        Edit::Move {
                            from: allocation,
                            to: spillslot,
                        },
                    ));
                    self.free_allocation_state(allocation);
                    self.set_allocation_state(vreg, allocation);
                    self.set_allocation_state(old_vreg, spillslot);
                }
                AllocationStep::Copy => {
                    debug_assert!(allocation_instruction.operand.kind() == OperandKind::Use);
                    debug_assert!(allocation_instruction.operand.vreg() != VReg::invalid());
                    let old_allocation = self.vreg_allocations[allocation_instruction.operand.vreg().vreg()];
                    let new_allocation = allocation_instruction.allocation;
                    debug_assert!(old_allocation != new_allocation);
                    self.edits.push((
                        ProgPoint::new(self.current_inst, InstPosition::Before),
                        Edit::Move {
                            from: old_allocation,
                            to: new_allocation,
                        },
                    ));
                }
            }
        }

        Ok(())
    }

    #[inline]
    fn find_scratch_reg(
        &self,
        reserved_reg_set: PRegSet,
        reg_class: RegClass,
    ) -> Option<PReg> {
        if let Some(preg) = self.mach_env.scratch_by_class[reg_class as usize] {
            if !reserved_reg_set.contains(preg) {
                return Some(preg);
            }
        }

        if let Some(preg) = self.find_free_preg(reg_class, reserved_reg_set) {
            return Some(preg);
        }

        None
    }

    #[inline]
    fn get_vreg_allocation(&self, vreg: VReg) -> Option<Allocation> {
        let allocation = self.vreg_allocations[vreg.vreg()];

        if allocation.is_some() {
            Some(allocation)
        } else {
            None
        }
    }

    #[inline]
    fn allocate_spillslot(&mut self, vreg: VReg) -> SpillSlot {
        let spillslots = &mut self.free_spillslots_per_class[vreg.class() as usize];
        if let Some(spillslot) = spillslots.pop() {
            return spillslot
        }

        let size = self.func.spillslot_size(vreg.class()) as u32;
        let mut offset = self.num_spillslots;
        // Align up to `size`.
        debug_assert!(size.is_power_of_two());
        offset = (offset + size - 1) & !(size - 1);
        let slot = if self.func.multi_spillslot_named_by_last_slot() {
            offset + size - 1
        } else {
            offset
        };
        offset += size;
        self.num_spillslots = offset;

        SpillSlot::new(slot as usize)
    }

    #[inline]
    fn get_allocation_vreg(&mut self, allocation: Allocation) -> Option<VReg> {
        if let Some(preg) = allocation.as_reg() {
            Some(self.preg_allocations[preg.index()].vreg)
        } else {
            if let Some(spillslot) = allocation.as_stack() {
                Some(self.spillslot_allocations[spillslot.index()])
            } else {
                None
            }
        }
    }

    #[inline]
    fn free_allocation_state(&mut self, allocation: Allocation) {
        let vreg = if let Some(preg) = allocation.as_reg() {
            self.allocated_pregs.remove(preg);
            self.preg_allocations[preg.index()].vreg
        } else {
            if let Some(spillslot) = allocation.as_stack() {
                let vreg = self.spillslot_allocations[spillslot.index()];
                self.spillslot_allocations[spillslot.index()] = VReg::invalid();
                self.free_spillslots_per_class[vreg.class() as usize].push(spillslot);
                vreg
            } else {
                return;
            }
        };
        self.vreg_allocations[vreg.vreg()] = Allocation::none();
    }

    #[inline]
    fn set_allocation_state(&mut self, vreg: VReg, allocation: Allocation) {
        self.vreg_allocations[vreg.vreg()] = allocation;
        if let Some(preg) = allocation.as_reg() {
            self.allocated_pregs.insert(preg);
            self.preg_allocations[preg.index()].vreg = vreg;
            self.preg_allocations[preg.index()].last_use = self.current_inst;
        }
        if let Some(spillslot) = allocation.as_stack() {
            self.spillslot_allocations[spillslot.index()] = vreg;
        }
    }

    #[inline]
    fn find_free_preg(&self, class: RegClass, blocked_pregs: PRegSet) -> Option<PReg> {
        for pregs in [
            &self.mach_env.preferred_regs_by_class[class as usize],
            &self.mach_env.non_preferred_regs_by_class[class as usize],
        ] {
            for &preg in pregs {
                if !blocked_pregs.contains(preg) {
                    return Some(preg);
                }
            }
        }

        None
    }

    #[inline]
    fn find_freeable_preg(&self, vreg: VReg, blocked_pregs: PRegSet) -> Result<PReg, RegAllocError> {
        let mut best_preg = PReg::invalid();
        let mut best_use = Inst::new(0);
        for pregs in [
            &self.mach_env.preferred_regs_by_class[vreg.class() as usize],
            &self.mach_env.non_preferred_regs_by_class[vreg.class() as usize],
        ] {
            for &preg in pregs {
                if blocked_pregs.contains(preg) {
                    continue;
                }

                let last_use = self.preg_allocations[preg.index()].last_use;
                if last_use <= best_use {
                    best_preg = preg;
                    best_use = last_use;
                }
            }
        }

        if best_preg.is_invalid() {
            return Err(RegAllocError::TooManyLiveRegs);
        }

        Ok(best_preg)
    }
}
