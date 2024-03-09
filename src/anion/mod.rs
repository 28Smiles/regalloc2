use std::iter::FromIterator;
use std::vec;
use std::vec::Vec;

use smallvec::SmallVec;

use preg_state::PRegState;
use vreg_tracker::VRegTracker;

use crate::{Allocation, Block, Edit, Function, Inst, InstPosition, InstRange, MachineEnv, OperandConstraint, OperandKind, OperandPos, Output, PReg, PRegSet, ProgPoint, RegAllocError, RegClass, SpillSlot, VReg};
use crate::anion::offset_vec::OffsetVec;
use crate::anion::spillslot_state::SpillSlotState;

mod offset_vec;
mod preg_state;
mod spillslot_state;
mod vreg_tracker;

struct State {
    pub block: Block,
    pub inst_range: InstRange,
    pub inst: Inst,
    pub pos: InstPosition,
}

impl Default for State {
    #[inline]
    fn default() -> Self {
        Self {
            block: Block::new(0),
            inst_range: InstRange::new(Inst::new(0), Inst::new(1)),
            inst: Inst::new(0),
            pos: InstPosition::After,
        }
    }
}

struct Edits(Vec<(ProgPoint, Edit)>);

impl Edits {
    #[inline]
    pub fn new(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity))
    }

    #[inline]
    pub fn push(&mut self, state: &State, edit: Edit) {
        self.0.push((ProgPoint::new(state.inst, state.pos), edit));
    }

    #[inline]
    pub fn push_multi<const N: usize>(&mut self, state: &State, edits: [Edit; N]) {
        for i in (0..N).rev() {
            self.push(state, edits[i]);
        }
    }

    #[inline]
    pub fn edits(mut self) -> Vec<(ProgPoint, Edit)> {
        self.0.reverse();
        self.0.sort_by_key(|(point, _)| *point);

        self.0
    }
}

struct Tracker<'a, F: Function> {
    preg_state: PRegState<'a>,
    spillslot_state: SpillSlotState<'a, F>,
    vreg_tracker: VRegTracker,
}

impl<'a, F: Function> Tracker<'a, F> {
    #[inline]
    pub fn new(func: &'a F, mach_env: &'a MachineEnv) -> Self {
        let preg_state = PRegState::new(mach_env);
        let spillslot_state = SpillSlotState::new(func);
        let vreg_tracker = VRegTracker::new(func);
        Self {
            preg_state,
            spillslot_state,
            vreg_tracker,
        }
    }

    /// Free a vreg allocation.
    #[inline]
    pub fn free(&mut self, vreg: VReg) {
        let allocation = self.vreg_tracker.get(vreg);
        if let Some(allocation) = allocation {
            // Is allocated.
            if let Some(preg) = allocation.as_reg() {
                self.preg_state.deallocate(preg);
            } else if let Some(spillslot) = allocation.as_stack() {
                self.spillslot_state.deallocate(spillslot);
            }
            self.vreg_tracker.set(vreg, Allocation::none());
        }
    }

    /// Allocate a vreg.
    #[inline]
    pub fn allocate(&mut self, state: &State, vreg: VReg, allocation: Allocation) {
        if let Some(preg) = allocation.as_reg() {
            self.preg_state.allocate(vreg, preg, state.inst);
        } else if let Some(spillslot) = allocation.as_stack() {
            self.spillslot_state.allocate(vreg, spillslot);
        }
        self.vreg_tracker.set(vreg, allocation);
    }

    /// Find a free preg.
    #[inline]
    pub fn find_free_preg(&self, reg_class: RegClass, ignore: PRegSet) -> Option<PReg> {
        self.preg_state.find_free(reg_class, ignore)
    }

    /// Find a furthest used preg.
    #[inline]
    pub fn find_furthest_use_preg(&self, reg_class: RegClass, ignore: PRegSet) -> Option<PReg> {
        self.preg_state.find_furthest_use(reg_class, ignore)
    }

    /// Find a free spillslot.
    #[inline]
    pub fn reserve_spillslot(&mut self, reg_class: RegClass) -> SpillSlot {
        self.spillslot_state.reserve(reg_class)
    }

    #[inline]
    pub fn in_reg(&self, vreg: VReg) -> bool {
        self.vreg_tracker.get(vreg)
            .map(|allocation| allocation.is_reg())
            .unwrap_or(false)
    }
}

trait Find<K, V> {
    fn find(&self, key: K) -> V;
}

impl<'a, F: Function> Find<VReg, Option<Allocation>> for Tracker<'a, F> {
    #[inline]
    fn find(&self, key: VReg) -> Option<Allocation> {
        self.vreg_tracker.get(key)
    }
}

impl<'a, F: Function> Find<Allocation, Option<VReg>> for Tracker<'a, F> {
    #[inline]
    fn find(&self, key: Allocation) -> Option<VReg> {
        if let Some(preg) = key.as_reg() {
            self.preg_state.find(preg).map(|(vreg, _)| vreg)
        } else if let Some(spillslot) = key.as_stack() {
            self.spillslot_state.find(spillslot)
        } else {
            None
        }
    }
}

impl<'a, F: Function> Find<PReg, Option<VReg>> for Tracker<'a, F> {
    #[inline]
    fn find(&self, key: PReg) -> Option<VReg> {
        self.preg_state.find(key).map(|(vreg, _)| vreg)
    }
}

impl<'a, F: Function> Find<SpillSlot, Option<VReg>> for Tracker<'a, F> {
    #[inline]
    fn find(&self, key: SpillSlot) -> Option<VReg> {
        self.spillslot_state.find(key)
    }
}

struct Anion<'a, F: Function> {
    func: &'a F,
    mach_env: &'a MachineEnv,
    tracker: Tracker<'a, F>,
    block_params: OffsetVec<Allocation>,
    allocations: OffsetVec<Allocation>,
    edits: Edits,
    state: State,
    done_processing: Vec<u64>,
}

impl<'a, F: Function> Anion<'a, F> {
    #[inline]
    pub fn new(func: &'a F, mach_env: &'a MachineEnv) -> Self {
        let block_params = OffsetVec::new(
            (0..func.num_blocks()).map(|block| func.block_params(Block::new(block)).len() as u32)
        );
        let allocations = OffsetVec::new(
            (0..func.num_insts()).map(|inst| func.inst_operands(Inst::new(inst)).len() as u32)
        );

        Self {
            func,
            mach_env,
            tracker: Tracker::new(func, mach_env),
            block_params,
            allocations,
            edits: Edits::new(func.num_insts() * 4),
            state: State::default(),
            done_processing: vec![0; func.num_blocks() / 64 + 1],
        }
    }

    pub fn run(mut self) -> Result<Output, RegAllocError> {
        // The allocator is a simple linear allocator, that runs backwards through the instructions.
        // This trick is used to remove the need for life range tracking.
        for block in (0..self.func.num_blocks()).rev() {
            let block = Block::new(block);
            let last_inst = self.func.block_insns(block).last();
            if self.func.is_ret(last_inst) {
                self.process_block(block)?;
            }
        }

        debug_assert!(
            (0..self.func.num_blocks()).all(|block| self.is_done_processing(Block::new(block))),
            "Not all blocks are processed"
        );

        let num_spillslots = self.tracker.spillslot_state.num_spillslots() as usize;
        let edits = self.edits.edits();
        let (inst_alloc_offsets, allocs) = self.allocations.into_inner();

        Ok(Output {
            num_spillslots,
            edits,
            inst_alloc_offsets,
            allocs,
            safepoint_slots: vec![],
            debug_locations: vec![],
            stats: Default::default(),
        })
    }

    #[inline]
    fn done_processing(&mut self, block: Block) {
        self.done_processing[block.index() / 64] |= 1 << (block.index() % 64);
    }

    #[inline]
    fn is_done_processing(&self, block: Block) -> bool {
        self.done_processing[block.index() / 64] & (1 << (block.index() % 64)) != 0
    }

    fn process_block(&mut self, block: Block) -> Result<(), RegAllocError> {
        if self.is_done_processing(block) {
            return Ok(());
        }

        self.state.block = block;
        self.state.inst_range = self.func.block_insns(block);
        self.state.inst = self.state.inst_range.last();
        self.state.pos = InstPosition::After;
        self.process_insts()?;
        self.done_processing(block);

        // for inst in self.state.inst_range.iter() {
        //     for &operand in self.func.inst_operands(inst) {
        //         self.tracker.free(operand.vreg());
        //     }
        // }

        for &prev in self.func.block_preds(block) {
            self.process_block(prev)?;
        }

        Ok(())
    }

    fn process_insts(&mut self) -> Result<(), RegAllocError> {
        debug_assert_eq!(self.state.inst, self.state.inst_range.last());
        debug_assert_eq!(self.state.pos, InstPosition::After);
        self.allocate_block_params();
        for inst in self.state.inst_range.iter().rev() {
            self.state.inst = inst;
            self.state.pos = InstPosition::After;
            self.allocate_operands()?;
        }
        self.state.pos = InstPosition::Before;
        self.place_block_params()?;

        Ok(())
    }

    fn allocate_block_params(&mut self) {
        debug_assert_eq!(self.state.inst, self.state.inst_range.last());
        for (idx, &succ) in self.func.block_succs(self.state.block).iter().enumerate() {
            let params = self.block_params.get_all(succ.index() as u32);
            let vregs = self.func.branch_blockparams(self.state.block, self.state.inst, idx);
            debug_assert_eq!(params.len(), vregs.len());
            for (&vreg, &allocation) in vregs.iter().zip(params.iter()) {
                self.tracker.allocate(&self.state, vreg, allocation);
            }
        }
    }

    fn place_block_params(&mut self) -> Result<(), RegAllocError> {
        debug_assert_eq!(self.state.inst, self.state.inst_range.first());
        debug_assert_eq!(self.state.pos, InstPosition::Before);
        // TODO: Check for use without def.
        // We first look at the branch instructions of the previous blocks, to determine
        // which pregs are used by the branch instructions. We then block these pregs
        // for the block parameters, so we don't allocate the same preg to the block
        // parameters and the branch instruction.
        let mut blocked_argument_slots = self.find_blocked_argument_slots()?;
        let arguments = self.func.block_params(self.state.block);

        // Stage 1: Just use the current allocation if it is a preg.
        for (idx, &arg) in arguments.iter().enumerate() {
            if let Some(current_allocation) = self.tracker.find(arg) {
                if let Some(preg) = current_allocation.as_reg() {
                    if !blocked_argument_slots.contains(preg) {
                        self.block_params.set(self.state.block.index() as u32, idx as u32, current_allocation);
                        blocked_argument_slots.add(preg);
                        continue;
                    }
                }
            }
        }

        // Stage 2: Allocate the arguments to pregs.
        for (idx, &arg) in arguments.iter().enumerate() {
            let block_param_allocation = self.block_params.get_mut(self.state.block.index() as u32, idx as u32);
            if (*block_param_allocation).is_some() {
                // The argument is already allocated.
                continue;
            }

            // Find a preg to allocate the argument to.
            let class = arg.class();
            if let Some(reg) = self.tracker.find_free_preg(class, blocked_argument_slots) {
                *block_param_allocation = Allocation::reg(reg);
                let block_param_allocation = *block_param_allocation;
                blocked_argument_slots.add(reg);
                self.move_vreg(arg, block_param_allocation, PRegSet::empty())?;
                continue;
            }
        }

        // Stage 3: Allocate the remaining arguments to spillslots.
        for (idx, &arg) in arguments.iter().enumerate() {
            let block_param_allocation = self.block_params.get_mut(self.state.block.index() as u32, idx as u32);
            if (*block_param_allocation).is_some() {
                // The argument is already allocated.
                continue;
            }

            *block_param_allocation = Allocation::stack(self.tracker.reserve_spillslot(arg.class()));
            let block_param_allocation = *block_param_allocation;
            self.move_vreg(arg, block_param_allocation, PRegSet::empty())?;
        }

        Ok(())
    }

    #[inline]
    fn find_blocked_argument_slots(&self) -> Result<PRegSet, RegAllocError> {
        debug_assert_eq!(self.state.inst, self.state.inst_range.first());
        // For each predecessor block, we need to block the pregs used by the last instruction.
        // The remaining pregs will be used to allocate the arguments. If there are not enough
        // pregs for the arguments, we will use spillslots for the remaining arguments.
        // -------------------------------------------------------------------------------------
        // We start by blocking all fixed pregs.
        let preds = self.func.block_preds(self.state.block);
        let mut blocked_pregs = PRegSet::empty();
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
                    let class = operand.class();
                    for preg in this_blocked_pregs.into_iter() {
                        if self.tracker.preg_state.regs_by_class(class).contains(preg) {
                            this_blocked_pregs.remove(preg);
                            continue 'operands;
                        }
                    }

                    // We didn't find a preg, we need reserve an additional preg.
                    let mut available_pregs = self.tracker.preg_state.regs_by_class(class);
                    available_pregs = available_pregs & !this_blocked_pregs.to_hw(class);
                    blocked_pregs.add(available_pregs.into_iter()
                        .next()
                        .map(|hw_enc| PReg::new(hw_enc, class))
                        .ok_or(RegAllocError::TooManyLiveRegs)?);
                }
            }
        }

        Ok(blocked_pregs)
    }

    fn allocate_operands(&mut self) -> Result<(), RegAllocError> {
        let operands = self.func.inst_operands(self.state.inst);
        let allocations = self.allocations.get_all_mut(self.state.inst.index() as u32);
        debug_assert_eq!(operands.len(), allocations.len());
        let mut allocation_orders: SmallVec<[_; 8]> = SmallVec::from_iter(0..operands.len());
        let tracker = &self.tracker;
        allocation_orders.sort_by_key(|&idx| {
            let operand = operands[idx];
            match (operand.constraint(), operand.kind(), operand.pos()) {
                // Start by allocating fixed registers, since we know they will always be allocated
                // and therefore prevent us from allocating to them in a later stage.
                (OperandConstraint::FixedReg(_), _, _) => 0,
                // Reuse operands are allocated next, since they will also prevent us from allocating
                // to them in a later stage.
                (OperandConstraint::Reuse(idx), OperandKind::Def, _) => match operands[idx].constraint() {
                    // Since a reuse operand needs the use to be allocated, we need to order them the same way.
                    OperandConstraint::FixedReg(_) => 1,
                    OperandConstraint::Reg
                    if tracker.in_reg(operand.vreg()) && operand.pos() == OperandPos::Late => 2,
                    OperandConstraint::Reg
                    if tracker.in_reg(operand.vreg()) => 3,
                    OperandConstraint::Reg => 4,
                    OperandConstraint::Any
                    if tracker.in_reg(operand.vreg()) && operand.pos() == OperandPos::Late => 5,
                    OperandConstraint::Any
                    if tracker.in_reg(operand.vreg()) => 6,
                    OperandConstraint::Any => 7,
                    OperandConstraint::Stack => 8,
                    _ => u8::MAX,
                },
                // Allocate stack operands before register operands, so regs may be freed.
                (OperandConstraint::Stack, OperandKind::Def, _) => 9,
                // We first allocate registers that are already allocated to a preg.
                (OperandConstraint::Reg, OperandKind::Def, OperandPos::Early)
                if tracker.in_reg(operand.vreg()) => 10,
                (OperandConstraint::Reg, OperandKind::Def, _)
                if tracker.in_reg(operand.vreg()) => 11,
                (OperandConstraint::Reg, OperandKind::Def, _) => 12,
                (OperandConstraint::Any, OperandKind::Def, OperandPos::Early)
                if tracker.in_reg(operand.vreg()) => 13,
                (OperandConstraint::Any, OperandKind::Def, _)
                if tracker.in_reg(operand.vreg()) => 14,
                (OperandConstraint::Any, OperandKind::Def, _) => 15,
                (OperandConstraint::Reg, OperandKind::Use, _)
                if operand.pos() == OperandPos::Late => 16,
                (OperandConstraint::Reg, OperandKind::Use, _) => 17,
                (OperandConstraint::Any, OperandKind::Use, _) => 18,
                (OperandConstraint::Stack, OperandKind::Use, _) => 19,
                _ => u8::MAX,
            }
        });

        let mut early_blocked_regs = PRegSet::empty();
        let mut late_blocked_regs = PRegSet::empty();
        self.save_vregs_from_clobbering()?;
        for idx in allocation_orders {
            self.allocate_operand(
                idx,
                &mut early_blocked_regs,
                &mut late_blocked_regs,
            )?;
        }
        self.update_vregs()?;
        self.state.pos = InstPosition::Before;
        self.handle_copies()?;

        Ok(())
    }

    #[inline]
    fn set_operand_allocation(&mut self, idx: usize, allocation: Allocation) {
        self.allocations.set(self.state.inst.index() as u32, idx as u32, allocation);
    }

    #[inline]
    fn get_operand_allocation(&mut self, idx: usize) -> Allocation {
        *self.allocations.get(self.state.inst.index() as u32, idx as u32)
    }

    #[inline]
    fn update_vregs(&mut self) -> Result<(), RegAllocError> {
        for &operand in self.func.inst_operands(self.state.inst) {
            if operand.kind() == OperandKind::Def && operand.as_fixed_nonallocatable().is_none() {
                if self.tracker.find(operand.vreg()).is_some() {
                    log::trace!("update_vregs: Freeing VReg {} from Allocation {}", operand.vreg(), self.tracker.find(operand.vreg()).unwrap());
                    self.tracker.free(operand.vreg());
                } else {
                    log::trace!("update_vregs: VReg {} is not allocated", operand.vreg());
                }
            }
        }
        for (idx, &operand) in self.func.inst_operands(self.state.inst).iter().enumerate() {
            if operand.kind() == OperandKind::Use && operand.as_fixed_nonallocatable().is_none() {
                let vreg = operand.vreg();
                if self.tracker.find(vreg).is_none() {
                    let allocation = self.get_operand_allocation(idx);
                    log::trace!("update_vregs: Allocating VReg {} to Allocation {}", vreg, allocation);
                    self.tracker.allocate(&self.state, vreg, allocation);
                }
            }
        }

        Ok(())
    }

    fn save_vregs_from_clobbering(
        &mut self,
    ) -> Result<(), RegAllocError> {
        let clobbered_regs = self.func.inst_clobbers(self.state.inst);
        for preg in clobbered_regs.into_iter() {
            if let Some(_) = self.tracker.find(preg) {
                // There is a vreg allocated to the preg.
                self.free_preg(preg, None, clobbered_regs)?;
            }
        }

        Ok(())
    }

    fn allocate_operand(
        &mut self,
        idx: usize,
        early_blocked_regs: &mut PRegSet,
        late_blocked_regs: &mut PRegSet,
    ) -> Result<(), RegAllocError> {
        debug_assert_eq!(self.state.pos, InstPosition::After);
        let operand = self.func.inst_operands(self.state.inst)[idx];
        log::trace!(
            "allocate_operand: Allocating operand with constraint {}, kind {:?} and vreg {}",
            operand.constraint(),
            operand.kind(),
            operand.vreg(),
        );
        match (operand.constraint(), operand.kind()) {
            (OperandConstraint::FixedReg(reg), OperandKind::Def) => {
                // The operand expects us to allocate a write to a specific register.
                // We must insert a move from the preg to the current vreg allocation,
                // if the preg is not already allocated to the vreg.
                // Since this is the def of the vreg, we can free the preg.
                // We set the allocation to the fixed preg, since we know it will be allocated.
                let allocation = Allocation::reg(reg);
                self.set_operand_allocation(idx, allocation);
                if let Some(vreg) = self.tracker.find(reg) {
                    if vreg == operand.vreg() {
                        log::trace!("allocate_operand: VReg {} already allocated to the correct preg {}", operand.vreg(), reg);
                        // The preg is already allocated to the correct vreg.
                        // We block the preg for further allocations in this instruction.
                        late_blocked_regs.add(reg);
                        return Ok(());
                    }
                    // The preg is already allocated to another vreg.
                    // We need to move the allocation.
                    log::trace!("allocate_operand: VReg {} already allocated to preg {}, free it", vreg, reg);
                    self.free_preg(reg, Some(operand.vreg()), *early_blocked_regs | *late_blocked_regs | self.func.inst_clobbers(self.state.inst))?;
                }
                debug_assert!(self.tracker.find(reg).is_none(), "Preg is already in use");
                // At this point, we know that the preg is free.
                // We can then connect the preg to the vreg.
                self.move_vreg(operand.vreg(), allocation, *early_blocked_regs | *late_blocked_regs)?;
                log::trace!("allocate_operand: {} moved to {}", operand.vreg(), allocation);
                late_blocked_regs.add(reg);
                if operand.pos() == OperandPos::Early {
                    early_blocked_regs.add(reg);
                }
            }
            (OperandConstraint::Reg, OperandKind::Def) => {
                // The operand expects us to allocate a write to a register.
                // We first handle the case where the vreg is already allocated to a preg.
                if let Some(preg) = self.tracker.find(operand.vreg()).and_then(|allocation| allocation.as_reg()) {
                    if !self.tracker.preg_state.stack_slots().contains(preg) && !self.func.inst_clobbers(self.state.inst).contains(preg) {
                        log::trace!("allocate_operand: VReg {} already allocated to a preg, allocate to {}", operand.vreg(), preg);
                        // The vreg is already allocated to a preg.
                        // We can then allocate the preg to the operand.
                        self.set_operand_allocation(idx, Allocation::reg(preg));
                        late_blocked_regs.add(preg);
                        if operand.pos() == OperandPos::Early {
                            early_blocked_regs.add(preg);
                        }
                        return Ok(());
                    }
                }

                // The vreg is not allocated to a preg.
                // We start by searching for a free preg to allocate to the vreg.
                let blocked_regs = if operand.pos() == OperandPos::Early {
                    *early_blocked_regs | *late_blocked_regs
                } else {
                    *late_blocked_regs
                } | self.func.inst_clobbers(self.state.inst);
                let preg = if let Some(preg) = self.tracker.find_free_preg(operand.class(), blocked_regs) {
                    log::trace!("allocate_operand: Found free preg {}", preg);
                    preg
                } else {
                    // We need to free a preg.
                    let preg = self.tracker.find_furthest_use_preg(operand.class(), blocked_regs)
                        .ok_or(RegAllocError::TooManyLiveRegs)?;
                    self.free_preg(preg, Some(operand.vreg()), blocked_regs)?;
                    log::trace!("allocate_operand: Freed preg {}", preg);

                    preg
                };

                let allocation = Allocation::reg(preg);
                self.set_operand_allocation(idx, allocation);
                self.move_vreg(operand.vreg(), allocation, *early_blocked_regs | *late_blocked_regs)?;
                log::trace!("allocate_operand: {} moved to {}", operand.vreg(), allocation);
                late_blocked_regs.add(preg);
                if operand.pos() == OperandPos::Early {
                    early_blocked_regs.add(preg);
                }
            }
            (OperandConstraint::Any, OperandKind::Def) => {
                // We can allocate the operand to any preg.
                // We attempt to allocate the operand to a preg if that fails,
                // we just allocate it to a spillslot.
                let blocked_regs = if operand.pos() == OperandPos::Early {
                    *early_blocked_regs | *late_blocked_regs
                } else {
                    *late_blocked_regs
                } | self.func.inst_clobbers(self.state.inst);
                if let Some(preg) = self.tracker.find(operand.vreg()).and_then(|allocation| allocation.as_reg()) {
                    if !blocked_regs.contains(preg) {
                        log::trace!("allocate_operand: VReg {} already allocated to a preg, allocate to {}", operand.vreg(), preg);
                        // The vreg is already allocated to a preg.
                        // We can then allocate the preg to the operand.
                        self.set_operand_allocation(idx, Allocation::reg(preg));
                        late_blocked_regs.add(preg);
                        if operand.pos() == OperandPos::Early {
                            early_blocked_regs.add(preg);
                        }
                        return Ok(());
                    }
                }

                // The vreg is not allocated to a preg.
                // We start by searching for a free preg to allocate to the vreg.

                if let Some(preg) = self.tracker.find_free_preg(operand.class(), blocked_regs) {
                    log::trace!("allocate_operand: Found free preg, move to {}", preg);
                    let allocation = Allocation::reg(preg);
                    self.set_operand_allocation(idx, allocation);
                    self.move_vreg(operand.vreg(), allocation, *early_blocked_regs | *late_blocked_regs)?;
                    late_blocked_regs.add(preg);
                    if operand.pos() == OperandPos::Early {
                        early_blocked_regs.add(preg);
                    }
                    return Ok(());
                }

                let spillslot = self.tracker.reserve_spillslot(operand.class());
                let allocation = Allocation::stack(spillslot);
                self.set_operand_allocation(idx, allocation);
                self.move_vreg(operand.vreg(), allocation, *early_blocked_regs | *late_blocked_regs)?;
                log::trace!("allocate_operand: VReg {} moved to spillslot {}", operand.vreg(), spillslot);
            }
            (OperandConstraint::Stack, OperandKind::Def) => {
                if let Some(preg) = self.tracker.find(operand.vreg()).and_then(|allocation| allocation.as_stack()) {
                    self.set_operand_allocation(idx, Allocation::stack(preg));
                    return Ok(());
                }

                let spillslot = self.tracker.reserve_spillslot(operand.class());
                let allocation = Allocation::stack(spillslot);
                self.set_operand_allocation(idx, allocation);
                self.move_vreg(operand.vreg(), allocation, *early_blocked_regs | *late_blocked_regs)?;
                log::trace!("allocate_operand: VReg {} moved to spillslot {}", operand.vreg(), spillslot);
            }
            (OperandConstraint::Reuse(_), OperandKind::Def) => {
                unimplemented!("Reuse operand");
            }
            (OperandConstraint::FixedReg(reg), OperandKind::Use) if operand.as_fixed_nonallocatable().is_some() => {
                // The operand expects us to allocate a read from a specific register.
                // This is a fixed non-allocatable operand, so we don't need to move any vregs.
                self.set_operand_allocation(idx, Allocation::reg(reg));
                early_blocked_regs.add(reg);
                if operand.pos() == OperandPos::Late {
                    late_blocked_regs.add(reg);
                }
            }
            (OperandConstraint::FixedReg(reg), OperandKind::Use) => {
                // The operand expects us to allocate a read from a specific register.
                // We must insert a move to the preg from the current vreg allocation,
                // if the preg is not already allocated to the vreg.
                // We set the allocation to the fixed preg, since we know it will be allocated.
                self.set_operand_allocation(idx, Allocation::reg(reg));
                // Find the current allocation of the preg.
                if let Some(vreg) = self.tracker.find(reg) {
                    if vreg == operand.vreg() {
                        log::trace!("allocate_operand: VReg {} already allocated to correct preg {}", operand.vreg(), reg);
                        // The preg is already allocated to the correct vreg.
                        early_blocked_regs.add(reg);
                        if operand.pos() == OperandPos::Late {
                            late_blocked_regs.add(reg);
                        }
                        return Ok(());
                    }
                    // The preg is already allocated to another vreg.
                    if operand.pos() == OperandPos::Early && late_blocked_regs.contains(reg) && !early_blocked_regs.contains(reg) {
                        log::trace!("allocate_operand: Preg {} already allocated to another vreg {} but is a definition, we can just reuse it.", reg, vreg);
                    } else {
                        // We need to move the allocation.
                        self.free_preg(reg, Some(operand.vreg()), *early_blocked_regs | *late_blocked_regs | self.func.inst_clobbers(self.state.inst))?;
                        log::trace!("allocate_operand: Preg {} already allocated to another vreg {}, freeing allocation.", reg, vreg);
                    }
                }

                // At this point, we know that the preg is free.
                // If we already know the vreg, we need to merge it, else we create a new allocation.
                if let Some(allocation) = self.tracker.find(operand.vreg()) {
                    log::trace!("allocate_operand: VReg {} already allocated to {}", operand.vreg(), allocation);
                    // We check if we can move the allocation cause it can live across the instruction.
                    let blocked = *early_blocked_regs | *late_blocked_regs; // Used by another operand def.
                    let clobbered = self.func.inst_clobbers(self.state.inst); // Clobbered by the instruction.
                    if !blocked.contains(reg) && !clobbered.contains(reg) {
                        log::trace!("allocate_operand: VReg {} can be moved to preg {}", operand.vreg(), reg);
                        // We can move the allocation.
                        self.move_vreg(operand.vreg(), Allocation::reg(reg), *early_blocked_regs | *late_blocked_regs)?;
                        debug_assert_eq!(self.tracker.find(reg), Some(operand.vreg()), "Allocation is not set");
                    } else {
                        // We keep the old allocation as a copy, we merge them with an edge
                        // In a later phase.
                    }
                } else {
                    // We don't know the vreg.
                    // We need to allocate the vreg to the preg.
                }

                early_blocked_regs.add(reg);
                if operand.pos() == OperandPos::Late {
                    late_blocked_regs.add(reg);
                }
            }
            (OperandConstraint::Reg, OperandKind::Use) => {
                // The operand expects us to allocate a read from a register.
                // We first handle the case where the vreg is already allocated to a preg.
                if let Some(preg) = self.tracker.find(operand.vreg()).and_then(|allocation| allocation.as_reg()) {
                    if !self.tracker.preg_state.stack_slots().contains(preg) {
                        // The vreg is already allocated to a preg.
                        // If we have reached the use stage of the allocation we know the preg is free early and late.
                        if !self.func.inst_clobbers(self.state.inst).contains(preg) {
                            log::trace!("allocate_operand: VReg {} already allocated to usable unclobbered preg {}", operand.vreg(), preg);
                            // We can then allocate the preg to the operand.
                            self.set_operand_allocation(idx, Allocation::reg(preg));
                            early_blocked_regs.add(preg);
                            if operand.pos() == OperandPos::Late {
                                late_blocked_regs.add(preg);
                            }
                            return Ok(());
                        }
                    }
                }

                // The vreg is not allocated to a preg.
                // We start by searching for a free preg to allocate to the vreg.
                let blocked_regs = if operand.pos() == OperandPos::Early {
                    *early_blocked_regs | *late_blocked_regs
                } else {
                    *late_blocked_regs
                } | self.func.inst_clobbers(self.state.inst);
                let reg = if let Some(reg) = self.tracker.find_free_preg(operand.class(), blocked_regs) {
                    log::trace!("allocate_operand: Found free preg {}", reg);
                    reg
                } else {
                    // We need to free a preg.
                    let reg = self.tracker.find_furthest_use_preg(operand.class(), blocked_regs)
                        .ok_or(RegAllocError::TooManyLiveRegs)?;
                    self.free_preg(reg, Some(operand.vreg()), blocked_regs)?;
                    log::trace!("allocate_operand: Freed preg {}", reg);

                    reg
                };
                debug_assert!(self.tracker.find(reg).is_none(), "Preg is already in use");
                // At this point, we know that the preg is free.
                // If we already know the vreg, we need to merge it, else we create a new allocation.
                if let Some(_) = self.tracker.find(operand.vreg()) {
                    // We check if we can move the allocation cause it can live across the instruction.
                    let blocked = *early_blocked_regs | *late_blocked_regs; // Used by another operand def.
                    let clobbered = self.func.inst_clobbers(self.state.inst); // Clobbered by the instruction.
                    if !blocked.contains(reg) && !clobbered.contains(reg) {
                        // We can move the allocation.
                        self.move_vreg(operand.vreg(), Allocation::reg(reg), *early_blocked_regs | *late_blocked_regs)?;
                        log::trace!("allocate_operand: VReg {} moved to preg {}", operand.vreg(), reg);
                        debug_assert_eq!(self.tracker.find(reg), Some(operand.vreg()), "Allocation is not set");
                    } else {
                        // We keep the old allocation as a copy, we merge them with an edge
                        // In a later phase.
                    }
                } else {
                    // We don't know the vreg.
                    // We need to allocate the vreg to the preg.
                }

                self.set_operand_allocation(idx, Allocation::reg(reg));
                early_blocked_regs.add(reg);
                if operand.pos() == OperandPos::Late {
                    late_blocked_regs.add(reg);
                }
            }
            (OperandConstraint::Any, OperandKind::Use) => {
                // The operand expects us to allocate a read from any place.
                if let Some(old_allocation) = self.tracker.find(operand.vreg()) {
                    // The vreg is already allocated.
                    if let Some(preg) = old_allocation.as_reg() {
                        // The vreg is already allocated to a preg.
                        // If we have reached the use stage of the allocation we know the preg is free early and late.
                        if !self.func.inst_clobbers(self.state.inst).contains(preg) {
                            log::trace!("allocate_operand: VReg {} already allocated to usable unclobbered preg {}", operand.vreg(), preg);
                            // We can then allocate the preg to the operand.
                            self.set_operand_allocation(idx, Allocation::reg(preg));
                            early_blocked_regs.add(preg);
                            if operand.pos() == OperandPos::Late {
                                late_blocked_regs.add(preg);
                            }
                            return Ok(());
                        }
                    } else {
                        // The vreg is already allocated to a spillslot.
                        self.set_operand_allocation(idx, old_allocation);
                        return Ok(());
                    }
                }

                // We start by searching for a free preg to allocate to the vreg.
                let blocked_regs = if operand.pos() == OperandPos::Early {
                    *early_blocked_regs | *late_blocked_regs
                } else {
                    *late_blocked_regs
                } | self.func.inst_clobbers(self.state.inst);
                let allocation = if let Some(reg) = self.tracker.find_free_preg(operand.class(), blocked_regs) {
                    log::trace!("allocate_operand: Found free preg {}", reg);
                    early_blocked_regs.add(reg);
                    if operand.pos() == OperandPos::Late {
                        late_blocked_regs.add(reg);
                    }

                    Allocation::reg(reg)
                } else {
                    log::trace!("allocate_operand: No free preg, allocate to spillslot");
                    Allocation::stack(self.tracker.reserve_spillslot(operand.class()))
                };
                self.set_operand_allocation(idx, allocation);

                if let Some(old_allocation) = self.tracker.find(operand.vreg()) {
                    debug_assert!(old_allocation.is_reg(), "Allocation is not a preg");
                    if let Some(reg) = allocation.as_reg() {
                        let blocked = *early_blocked_regs | *late_blocked_regs; // Used by another operand def.
                        let clobbered = self.func.inst_clobbers(self.state.inst); // Clobbered by the instruction.
                        if !blocked.contains(reg) && !clobbered.contains(reg) {
                            // We can move the allocation.
                            self.move_vreg(operand.vreg(), allocation, *early_blocked_regs | *late_blocked_regs)?;
                            log::trace!("allocate_operand: VReg {} moved to preg {}", operand.vreg(), reg);
                            debug_assert_eq!(self.tracker.find(reg), Some(operand.vreg()), "Allocation is not set");
                        } else {
                            // We keep the old allocation as a copy, we merge them with an edge
                            // In a later phase.
                        }
                    } else {
                        // We just move it into a spillslot.
                        self.move_vreg(operand.vreg(), allocation, *early_blocked_regs | *late_blocked_regs)?;
                        log::trace!("allocate_operand: VReg {} moved to spillslot", operand.vreg());
                        debug_assert_eq!(self.tracker.find(old_allocation.as_stack().unwrap()), Some(operand.vreg()), "Allocation is not set");
                    }
                } else {
                    // We don't know the vreg, we just allocate it.
                }
            }
            (OperandConstraint::Stack, OperandKind::Use) => {
                // The operand expects us to allocate a read from a spillslot.
                if let Some(old_allocation) = self.tracker.find(operand.vreg()) {
                    // The vreg is already allocated.
                    if old_allocation.is_stack() {
                        log::trace!("allocate_operand: VReg {} already allocated to spillslot", operand.vreg());
                        // The vreg is already allocated to a spillslot.
                        self.set_operand_allocation(idx, old_allocation);
                        return Ok(());
                    }
                }

                // We start by searching for a free spillslot to allocate to the vreg.
                let allocation = Allocation::stack(self.tracker.reserve_spillslot(operand.class()));
                self.set_operand_allocation(idx, allocation);
                if let Some(old_allocation) = self.tracker.find(operand.vreg()) {
                    debug_assert!(old_allocation.is_reg(), "Allocation is not a preg");
                    self.move_vreg(operand.vreg(), allocation, *early_blocked_regs | *late_blocked_regs)?;
                    log::trace!("allocate_operand: VReg {} moved to spillslot", operand.vreg());
                    debug_assert_eq!(self.tracker.find(old_allocation.as_stack().unwrap()), Some(operand.vreg()), "Allocation is not set");
                } else {
                    // We don't know the vreg, we just allocate it.
                }
            }
            _ => unimplemented!(),
        }

        Ok(())
    }

    fn handle_copies(&mut self) -> Result<(), RegAllocError> {
        debug_assert!(self.state.pos == InstPosition::Before);
        let operands = self.func.inst_operands(self.state.inst);
        let allocations = self.allocations.get_all(self.state.inst.index() as u32);
        debug_assert!(operands.len() == allocations.len());
        for (operand, allocation) in operands.iter().zip(allocations.iter()) {
            debug_assert!(allocation.is_some(), "Allocation is not set");
            let vreg = operand.vreg();
            if let Some(current_allocation) = self.tracker.find(vreg) {
                if current_allocation == *allocation {
                    continue;
                }

                if let (Some(from), Some(to)) = (current_allocation.as_reg(), allocation.as_reg()) {
                    if self.tracker.preg_state.stack_slots().contains(from) && self.tracker.preg_state.stack_slots().contains(to) {
                        // We cant move between spillslots.
                        // Use the spillslot as a temporary.
                        if let Some(scratch_reg) = self.mach_env.scratch_by_class[vreg.class() as usize] {
                            let scratch_reg = Allocation::reg(scratch_reg);
                            self.edits.push_multi(&self.state, [
                                Edit::Move { from: current_allocation, to: scratch_reg },
                                Edit::Move { from: scratch_reg, to: *allocation },
                            ]);
                            continue;
                        }

                        if let Some(free_preg) = self.tracker.find_free_preg(vreg.class(), PRegSet::empty()) {
                            let scratch_reg = Allocation::reg(free_preg);
                            self.edits.push_multi(&self.state, [
                                Edit::Move { from: current_allocation, to: scratch_reg },
                                Edit::Move { from: scratch_reg, to: *allocation },
                            ]);
                            continue;
                        }

                        let mut blocked_regs = PRegSet::empty();
                        blocked_regs.add(from);
                        blocked_regs.add(to);
                        let freeable_preg = self.tracker.find_furthest_use_preg(vreg.class(), blocked_regs)
                            .ok_or(RegAllocError::TooManyLiveRegs)?;
                        let freeable_vreg = self.tracker.find(freeable_preg).unwrap();
                        let scratch_reg = Allocation::reg(freeable_preg);
                        {
                            // Spill
                            let spillslot = Allocation::stack(self.tracker.reserve_spillslot(freeable_vreg.class()));
                            self.tracker.free(freeable_vreg);
                            self.tracker.allocate(&self.state, freeable_vreg, spillslot);
                            self.edits.push(&self.state, Edit::Move {
                                from: spillslot,
                                to: scratch_reg,
                            });
                        }
                        self.edits.push_multi(&self.state, [
                            Edit::Move { from: current_allocation, to: scratch_reg },
                            Edit::Move { from: scratch_reg, to: *allocation },
                        ]);
                        {
                            // Unspill
                            let spillslot = self.tracker.find(freeable_vreg).unwrap();
                            self.tracker.free(freeable_vreg);
                            self.tracker.allocate(&self.state, freeable_vreg, *allocation);
                            self.edits.push(&self.state, Edit::Move {
                                from: scratch_reg,
                                to: spillslot,
                            });
                        }
                        continue;
                    }
                }

                self.edits.push(&self.state, Edit::Move {
                    from: current_allocation,
                    to: *allocation,
                });
            }
        }

        Ok(())
    }

    /// Move a vreg to an allocation.
    /// This function will insert a move instruction, if the vreg is already allocated to a preg.
    /// This function will also update the vreg tracker.
    #[inline]
    fn move_vreg(&mut self, vreg: VReg, allocation: Allocation, blocked: PRegSet) -> Result<(), RegAllocError> {
        debug_assert!(self.tracker.find(allocation).is_none(), "Allocation is already in use");
        if let Some(old_allocation) = self.tracker.find(vreg) {
            // First check if the vreg is already allocated to the preg.
            if old_allocation == allocation {
                log::trace!("move_vreg: VReg {} already allocated to {}", vreg, allocation);
                return Ok(());
            }

            // We free the old allocation.
            self.tracker.free(vreg);
            // We allocate the new allocation.
            self.tracker.allocate(&self.state, vreg, allocation);
            // We insert a move instruction.
            if let (Some(from), Some(to)) = (old_allocation.as_reg(), allocation.as_reg()) {
                if self.tracker.preg_state.stack_slots().contains(from) && self.tracker.preg_state.stack_slots().contains(to) {
                    // We cant move between spillslots.
                    // Use the spillslot as a temporary.
                    if let Some(scratch_reg) = self.mach_env.scratch_by_class[vreg.class() as usize] {
                        let scratch_reg = Allocation::reg(scratch_reg);
                        log::trace!("move_vreg: Moving VReg {} to {} using scratch register {}", vreg, allocation, scratch_reg);
                        self.edits.push_multi(&self.state, [
                            Edit::Move { from: allocation, to: scratch_reg },
                            Edit::Move { from: scratch_reg, to: old_allocation },
                        ]);
                        return Ok(());
                    }

                    if let Some(free_preg) = self.tracker.find_free_preg(vreg.class(), blocked) {
                        let scratch_reg = Allocation::reg(free_preg);
                        log::trace!("move_vreg: Moving VReg {} to {} using scratch register {}", vreg, allocation, scratch_reg);
                        self.edits.push_multi(&self.state, [
                            Edit::Move { from: allocation, to: scratch_reg },
                            Edit::Move { from: scratch_reg, to: old_allocation },
                        ]);
                        return Ok(());
                    }

                    let mut blocked_regs = PRegSet::empty();
                    blocked_regs.add(from);
                    blocked_regs.add(to);
                    let freeable_preg = self.tracker.find_furthest_use_preg(vreg.class(), blocked_regs)
                        .ok_or(RegAllocError::TooManyLiveRegs)?;
                    let freeable_vreg = self.tracker.find(freeable_preg).unwrap();
                    let scratch_reg = Allocation::reg(freeable_preg);
                    log::trace!("move_vreg: Moving VReg {} to {} using spilled and reloaded scratch register {}", vreg, allocation, scratch_reg);
                    self.spill_preg(freeable_preg);
                    self.edits.push_multi(&self.state, [
                        Edit::Move { from: allocation, to: scratch_reg },
                        Edit::Move { from: scratch_reg, to: old_allocation },
                    ]);
                    self.move_vreg(freeable_vreg, scratch_reg, blocked)?;
                }
            }

            self.edits.push(&self.state, Edit::Move {
                from: allocation,
                to: old_allocation,
            });
        }

        Ok(())
    }

    /// Free a preg allocation.
    /// This will try multiple methods to free the preg.
    /// 1. Find a free preg to move the allocation to.
    /// 2. Attempt a swap with another (v)reg. (needs a scratch register)
    /// 3. Spill the allocation to a spillslot.
    #[inline]
    fn free_preg(
        &mut self,
        preg: PReg,
        swap_candidate: Option<VReg>,
        ignore: PRegSet,
    ) -> Result<(), RegAllocError> {
        debug_assert!(self.tracker.find(preg).is_some(), "Preg is not allocated");
        let vreg = self.tracker.find(preg).unwrap();
        if let Some(free_preg) = self.tracker.find_free_preg(preg.class(), ignore) {
            // We found a free preg to move the allocation to.
            log::trace!("free_preg: Found free preg {} to move allocation to", free_preg);
            self.move_vreg(vreg, Allocation::reg(free_preg), ignore)?;
            return Ok(());
        }

        if let Some(swap_candidate) = swap_candidate {
            // We found a swap candidate and a scratch register.
            if swap_candidate.class() == preg.class() {
                // The swap candidate is of the same class as the preg.
                if let Some(scratch_reg) = self.mach_env.scratch_by_class[preg.class() as usize] {
                    let candidate_allocation = self.tracker.find(swap_candidate).unwrap();
                    // We found a swap candidate and a scratch register.
                    log::trace!("free_preg: Found swap candidate {} and scratch register {} to swap allocation with", swap_candidate, scratch_reg);
                    self.swap(
                        candidate_allocation,
                        Allocation::reg(preg),
                        scratch_reg
                    );
                    return Ok(());
                }
            }
        }

        // We need to spill the allocation to a spillslot.
        self.spill_preg(preg);

        Ok(())
    }

    #[inline]
    fn swap(
        &mut self,
        a: Allocation,
        b: Allocation,
        scratch_reg: PReg,
    ) {
        let scratch_reg = Allocation::reg(scratch_reg);
        log::trace!("swap: Swapping allocation {} with {} using scratch register {}", a, b, scratch_reg);
        // We update the vreg tracker.
        let vreg_a = self.tracker.find(a).unwrap();
        let vreg_b = self.tracker.find(b).unwrap();
        self.tracker.free(vreg_a);
        self.tracker.free(vreg_b);
        self.tracker.allocate(&self.state, vreg_a, b);
        self.tracker.allocate(&self.state, vreg_b, a);
        // We insert a swap instructions.
        self.edits.push_multi(&self.state, [
            Edit::Move { from: a, to: scratch_reg },
            Edit::Move { from: b, to: a },
            Edit::Move { from: scratch_reg, to: b },
        ]);
    }

    #[inline]
    fn spill_preg(&mut self, preg: PReg) {
        let vreg = self.tracker.find(preg).unwrap();
        let spillslot = Allocation::stack(self.tracker.reserve_spillslot(vreg.class()));
        log::trace!("spill_preg: Spilling allocation {} to spillslot {}", preg, spillslot);
        self.tracker.free(vreg);
        self.tracker.allocate(&self.state, vreg, spillslot);
        self.edits.push(&self.state, Edit::Move {
            from: spillslot,
            to: Allocation::reg(preg),
        });
    }
}

pub fn run<F: Function>(
    func: &F,
    mach_env: &MachineEnv,
) -> Result<Output, RegAllocError> {
    let env = Anion::new(func, mach_env);

    env.run()
}

#[cfg(all(test, feature = "fuzzing"))]
mod test {
    use super::*;
    use std::{println, vec};

    use crate::fuzzing::func::{Func, FuncBuilder, InstData, InstOpcode, machine_env};
    use crate::{Operand, OperandConstraint, OperandKind, OperandPos, RegClass};
    use crate::fuzzing::arbitrary::{Arbitrary, Unstructured};

    #[test]
    fn test() {
        let env = machine_env();
        let mut func = FuncBuilder::new();
        let b1 = func.add_block();
        let v0 = func.add_vreg(RegClass::Float);
        let v1 = func.add_vreg(RegClass::Float);
        func.add_inst(b1, InstData::op(vec![
            Operand::new(v0, OperandConstraint::Reg, OperandKind::Def, OperandPos::Late),
            Operand::new(v1, OperandConstraint::Reg, OperandKind::Def, OperandPos::Late),
        ]));
        let v2 = func.add_vreg(RegClass::Float);
        let v3 = func.add_vreg(RegClass::Float);
        func.add_inst(b1, InstData::op(vec![
            Operand::new(v2, OperandConstraint::Reg, OperandKind::Def, OperandPos::Late),
            Operand::new(v3, OperandConstraint::Reg, OperandKind::Def, OperandPos::Late),
        ]));
        let v4 = func.add_vreg(RegClass::Float);
        func.add_inst(b1, InstData::op(vec![
            Operand::new(v0, OperandConstraint::Reg, OperandKind::Use, OperandPos::Early),
            Operand::new(v2, OperandConstraint::Reg, OperandKind::Use, OperandPos::Early),
            Operand::new(v4, OperandConstraint::Reg, OperandKind::Def, OperandPos::Late),
        ]));
        let v5 = func.add_vreg(RegClass::Float);
        func.add_inst(b1, InstData::op(vec![
            Operand::new(v1, OperandConstraint::Reg, OperandKind::Use, OperandPos::Early),
            Operand::new(v2, OperandConstraint::Reg, OperandKind::Use, OperandPos::Early),
            Operand::new(v3, OperandConstraint::Reg, OperandKind::Use, OperandPos::Early),
            Operand::new(v5, OperandConstraint::Reg, OperandKind::Def, OperandPos::Late),
        ]));
        func.add_inst(b1, InstData::branch());
        func.set_block_params_out(b1, vec![vec![v4, v5]]);
        let b2 = func.add_block();
        let v6 = func.add_vreg(RegClass::Float);
        let v7 = func.add_vreg(RegClass::Float);
        func.set_block_params_in(b2, &vec![v6, v7]);
        let v8 = func.add_vreg(RegClass::Float);
        func.add_inst(b2, InstData::op(vec![
            Operand::new(v6, OperandConstraint::Reg, OperandKind::Use, OperandPos::Early),
            Operand::new(v7, OperandConstraint::Reg, OperandKind::Use, OperandPos::Early),
            Operand::new(v8, OperandConstraint::Reg, OperandKind::Def, OperandPos::Late),
        ]));
        func.add_inst(b2, InstData {
            op: InstOpcode::Ret,
            operands: vec![Operand::new(v8, OperandConstraint::Reg, OperandKind::Use, OperandPos::Early)],
            clobbers: vec![],
            is_safepoint: false,
        });
        func.add_edge(b1, b2);
        let func = func.finalize();
        println!("{:?}", &func);
        let result = run(&func, &env).unwrap();
        println!("{:?}", result);
        let mut checker = crate::checker::Checker::new(&func, &env);
        checker.prepare(&result);
        checker.run().unwrap();
    }

    #[test]
    fn arbitrary() {
        let env = machine_env();
        let func = Func::arbitrary(&mut Unstructured::new([4,5,6,7,3,2,6,8,9,3,2].as_slice())).unwrap();
        println!("{:?}", &func);
        let result = run(&func, &env).unwrap();
        println!("{:?}", result);
        let mut checker = crate::checker::Checker::new(&func, &env);
        checker.prepare(&result);
        checker.run().unwrap();
    }
}