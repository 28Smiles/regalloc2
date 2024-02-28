use std::cmp::{max, min};
use std::collections::BTreeMap;
use std::iter::Peekable;
use std::{format, vec};
use std::prelude::rust_2015::ToString;
use std::vec::Vec;
use hashbrown::HashSet;
use smallvec::SmallVec;

use crate::{Allocation, Block, Edit, Function, Inst, InstPosition, InstRange, MachineEnv, Operand, OperandConstraint, OperandKind, Output, PReg, PRegSet, ProgPoint, RegAllocError, RegClass, SpillSlot, VReg};

struct DebugLocations {
    // (vreg, point) -> debug label
    debug_ranges: BTreeMap<u64, u32>,
    // (debug label, point) -> allocation
    vreg_allocations: BTreeMap<u64, Allocation>,
}

impl DebugLocations {
    #[inline]
    pub fn new(debug_value_labels: &[(VReg, Inst, Inst, u32)]) -> Self {
        let mut needs_debug = BTreeMap::new();
        for (vreg, start, end, label) in debug_value_labels.iter().copied() {
            let start_index = Self::pack(vreg, ProgPoint::new(start, InstPosition::Before), true);
            let end_index = Self::pack(vreg, ProgPoint::new(end, InstPosition::Before), false);
            needs_debug.insert(start_index, label);
            needs_debug.insert(end_index, label);
        }

        Self {
            debug_ranges: needs_debug,
            vreg_allocations: BTreeMap::new(),
        }
    }

    #[inline(always)]
    fn pack_vreg(vreg: VReg) -> u32 {
        ((vreg.vreg() as u32) << 2) | (vreg.class() as u8 as u32)
    }

    #[inline(always)]
    fn unpack_vreg(index: u32) -> VReg {
        let vreg = (index >> 2) as usize;
        let class = match index & 0b11 {
            0 => RegClass::Int,
            1 => RegClass::Float,
            2 => RegClass::Vector,
            _ => unreachable!(),
        };

        VReg::new(vreg, class)
    }

    #[inline(always)]
    fn pack(vreg: VReg, point: ProgPoint, is_start: bool) -> u64 {
        let vreg = (Self::pack_vreg(vreg) as u64) << 33;
        let point = (point.to_index() as u64) << 1;
        let is_start = if is_start { 0 } else { 1 };

        vreg | point | is_start
    }

    #[inline(always)]
    fn unpack(index: u64) -> (VReg, ProgPoint, bool) {
        let vreg = Self::unpack_vreg((index >> 33) as u32);
        let point = ProgPoint::from_index((index >> 1) as u32);
        let is_start = (index & 1) != 0;

        (vreg, point, is_start)
    }

    #[inline]
    pub fn insert(
        &mut self,
        vreg: VReg,
        point: ProgPoint,
        allocation: Allocation,
    ) {
        let index = ((Self::pack_vreg(vreg) as u64) << 33) | 0x0001FFFF;
        if let Some((&last_index, _)) = self.debug_ranges.range(..=index).next_back() {
            let (debug_vreg, _, _) = Self::unpack(last_index);
            if vreg != debug_vreg {
                return; // We only need to insert information for vregs that need debug information
            }
        }

        let index = Self::pack(vreg, point, true);
        if let Some((&last_index, &last_allocation)) = self.vreg_allocations.range(..=index).next_back() {
            let (vreg, _, _) = Self::unpack(last_index);
            if last_allocation != allocation || vreg != vreg {
                // We only need to insert a new debug location if the allocation has changed
                self.vreg_allocations.insert(index, allocation);
            }
        } else {
            self.vreg_allocations.insert(index, allocation);
        }
    }

    #[inline]
    pub fn get_debug_locations(&self, last_instruction: Inst) -> Vec<(u32, ProgPoint, ProgPoint, Allocation)> {
        if self.vreg_allocations.is_empty() || self.debug_ranges.is_empty() {
            return vec![];
        }

        struct DebugLocationIterator<'a, I: Iterator<Item = (&'a u64, &'a u32)>>(I);
        impl<'a, I: Iterator<Item = (&'a u64, &'a u32)>> Iterator for DebugLocationIterator<'a, I> {
            type Item = (VReg, ProgPoint, ProgPoint, u32);
            fn next(&mut self) -> Option<Self::Item> {
                let (&index_start, &label) = self.0.next()?;
                let (&index_end, _) = self.0.next()?;
                let (vreg, start, _) = DebugLocations::unpack(index_start);
                let (_, end, _) = DebugLocations::unpack(index_end);

                Some((vreg, start, end, label))
            }
        }
        struct VRegLocationIterator<'a, I: Iterator<Item = (&'a u64, &'a Allocation)>>(Peekable<I>, Inst);
        impl<'a, I: Iterator<Item = (&'a u64, &'a Allocation)>> Iterator for VRegLocationIterator<'a, I> {
            type Item = (VReg, ProgPoint, ProgPoint, Allocation);
            fn next(&mut self) -> Option<Self::Item> {
                let (&index_start, &allocation) = self.0.next()?;
                let (vreg, start, _) = DebugLocations::unpack(index_start);

                let (&index_end, &allocation_end) = self.0.peek()?;
                let (vreg_end, end, _) = DebugLocations::unpack(index_end);
                if vreg != vreg_end {
                    // Open range
                    return Some((vreg, start, ProgPoint::new(self.1, InstPosition::After), allocation));
                }
                if allocation_end.is_none() {
                    // This is the end of the range
                    self.0.next();
                }

                return Some((vreg, start, end, allocation));
            }
        }

        let mut debug_locations = Vec::with_capacity(self.vreg_allocations.len() * 2);
        let mut vreg_allocations = VRegLocationIterator(self.vreg_allocations.iter().peekable(), last_instruction);
        let mut debug_ranges = DebugLocationIterator(self.debug_ranges.iter());
        let mut debug_range = debug_ranges.next().unwrap();
        let mut vreg_allocation = vreg_allocations.next().unwrap();
        loop {
            let (vreg, start, end, label) = debug_range;
            let (vreg_alloc, alloc_start, alloc_end, allocation) = vreg_allocation;
            // If the debug range is before the vreg allocation, we need to advance the debug range
            if vreg < vreg_alloc {
                debug_range = if let Some(debug_range) = debug_ranges.next() {
                    debug_range
                } else {
                    break;
                }
            }

            // If the vreg allocation is before the debug range, we need to advance the vreg allocation
            if vreg > vreg_alloc {
                vreg_allocation = if let Some(vreg_allocation) = vreg_allocations.next() {
                    vreg_allocation
                } else {
                    break;
                }
            }

            // Check if the ranges overlap
            if start < alloc_end && end > alloc_start {
                debug_locations.push((label, max(start, alloc_start), min(end, alloc_end), allocation));
            }

            // Advance the allocation if the end of the allocation is before the end of the debug range
            if alloc_end < end {
                vreg_allocation = if let Some(vreg_allocation) = vreg_allocations.next() {
                    vreg_allocation
                } else {
                    break;
                }
            } else {
                debug_range = if let Some(debug_range) = debug_ranges.next() {
                    debug_range
                } else {
                    break;
                }
            }
        }

        debug_locations
    }
}

struct Env<'a, F: Function> {
    func: &'a F,
    mach_env: &'a MachineEnv,

    num_spillslots: u32,
    edits: Vec<(ProgPoint, Edit)>,
    inst_alloc_offsets: Vec<u32>,
    allocs: Vec<Allocation>,
    // Variables used during the allocation
    /// A map from vreg index to the current allocation.
    allocated_vregs: Vec<VReg>,
    vreg_allocations: Vec<Allocation>,
    /// The offsets of the allocations in the `blockparam_allocations` array.
    blockparam_allocation_offsets: Vec<usize>,
    /// A map from block parameters to the expected allocations before jumping to the block.
    blockparam_allocations: Vec<Allocation>,
    /// Last vreg use.
    last_vreg_use: Vec<Inst>,
    /// Pregs that are reserved for the current instruction.
    reserved_pregs: PRegSet,
    /// The vregs that are in the preg.
    preg_vregs: Vec<VReg>,
    /// The last use of a preg.
    preg_last_use: Vec<Inst>,
    /// Allocated but free spill slots per class.
    free_spill_slots: [Vec<SpillSlot>; 3],

    // State
    current_block: Block,
    current_block_inst_range: InstRange,
    current_inst: Inst,
}

impl<'a, F: Function> Env<'a, F> {
    #[inline]
    pub fn new(func: &'a F, mach_env: &'a MachineEnv) -> Self {
        let alloc_count = (0..func.num_insts()).into_iter()
            .map(|i| func.inst_operands(Inst::new(i)).len())
            .sum();
        let mut inst_alloc_offsets = Vec::with_capacity(func.num_insts());
        let mut alloc_offsets = 0;
        for i in 0..func.num_insts() {
            inst_alloc_offsets.push(alloc_offsets);
            alloc_offsets += func.inst_operands(Inst::new(i)).len() as u32;
        }
        let mut blockparam_allocation_offsets = Vec::with_capacity(func.num_blocks());
        let mut blockparam_allocation_count = 0;
        for block in 0..func.num_blocks() {
            blockparam_allocation_offsets.push(blockparam_allocation_count);
            blockparam_allocation_count += func.block_params(Block::new(block)).len();
        }

        Self {
            func,
            mach_env,
            num_spillslots: 0,
            edits: Vec::with_capacity(alloc_count * 2),
            inst_alloc_offsets,
            allocs: vec![Allocation::none(); alloc_count],
            // Variables used during the allocation
            allocated_vregs: Vec::with_capacity(func.num_vregs()),
            vreg_allocations: vec![Allocation::none(); func.num_vregs()],
            blockparam_allocation_offsets: vec![0; func.num_blocks()],
            blockparam_allocations: vec![Allocation::none(); blockparam_allocation_count],
            last_vreg_use: vec![Inst::invalid(); func.num_vregs()],
            reserved_pregs: PRegSet::empty(),
            preg_vregs: vec![VReg::invalid(); mach_env.num_regs()],
            preg_last_use: vec![Inst::invalid(); mach_env.num_regs()],
            free_spill_slots: [
                Vec::with_capacity(32),
                Vec::with_capacity(32),
                Vec::with_capacity(32),
            ],
            // State
            current_block: func.entry_block(),
            current_block_inst_range: func.block_insns(func.entry_block()),
            current_inst: func.block_insns(func.entry_block()).first(),
        }
    }

    #[inline]
    fn run(
        mut self,
    ) -> Result<Output, RegAllocError> {
        let mut discovered_blocks = HashSet::with_capacity(self.func.num_blocks() * 4);
        let mut next_blocks = Vec::with_capacity(self.func.num_blocks());
        // Generate allocations for all blocks
        // We start with the entry block and then discover all blocks successors and so on
        next_blocks.push(self.func.entry_block());
        while let Some(block) = next_blocks.pop() {
            // Skip blocks we have already processed
            if discovered_blocks.contains(&block) {
                continue;
            }
            // Mark the block as processed
            discovered_blocks.insert(block);
            // Set the current block
            self.current_block = block;
            self.current_block_inst_range = self.func.block_insns(block);
            self.current_inst = self.current_block_inst_range.first();
            self.setup_block_state(block);
            // Allocate the block
            for inst in self.current_block_inst_range.iter() {
                // Set the current instruction
                self.current_inst = inst;
                // Allocate the instruction
                self.allocate_operands()?;
                // Handle branches
                if self.func.is_branch(inst) {
                    self.block_branch_allocations()?; // Allocate the branch arguments
                    self.handle_branch()?; // Handle the branch
                }
            }
            // Add the successors to the queue
            next_blocks.extend(self.func.block_succs(block));
        }

        // Sort the edits by point
        self.edits.sort_by_key(|(point, _)| point.bits);
        Ok(Output {
            num_spillslots: self.num_spillslots as usize,
            edits: self.edits,
            allocs: self.allocs,
            inst_alloc_offsets: self.inst_alloc_offsets,
            safepoint_slots: vec![],
            debug_locations: vec![],
            stats: Default::default(),
        })
    }

    #[inline]
    fn setup_block_state(&mut self, block: Block) {
        self.current_block = block;
        self.current_block_inst_range = self.func.block_insns(block);
        // Free all allocations
        for vreg in &self.allocated_vregs {
            let allocation = self.vreg_allocations[vreg.vreg()];
            if let Some(spill_slot) = allocation.as_stack() {
                self.free_spill_slots[vreg.class() as usize].push(spill_slot);
            }
            self.vreg_allocations[vreg.index()] = Allocation::none();
        }
        self.allocated_vregs.clear();
        self.reserved_pregs = PRegSet::empty();
        // Allocate the block parameters
        for (&allocation, &vreg) in self.block_parameter_allocations(block)
            .iter().zip(self.func.block_params(block).iter()) {
            self.allocate_override(vreg, allocation);
        }
    }

    #[inline]
    fn allocate_override(&mut self, vreg: VReg, allocation: Allocation) {
        self.vreg_allocations[vreg.index()] = allocation;
        self.allocated_vregs.push(vreg);
        if let Some(preg) = allocation.as_reg() {
            self.preg_vregs[preg.index()] = vreg;
            self.reserved_pregs.add(preg);
            self.preg_last_use[preg.index()] = self.current_inst;
        }
    }

    #[inline]
    fn block_parameter_allocations(&self, block: Block) -> &[Allocation] {
        let offset = self.blockparam_allocation_offsets[block.index()];
        let end = self.blockparam_allocation_offsets.get(block.index() + 1)
            .copied()
            .unwrap_or(self.blockparam_allocations.len());
        &self.blockparam_allocations[offset..end]
    }

    /// Find a preg for the given class
    ///  - `class` is the register class
    ///  - `blocked_pregs` is the set of pregs that are blocked and can't be used
    #[inline]
    fn find_preg_candidate(
        &mut self,
        class: RegClass,
        blocked_pregs: PRegSet,
    ) -> Result<PReg, RegAllocError> {
        let mut used_pregs = blocked_pregs;
        used_pregs.union_from(self.reserved_pregs);
        let mut preg_found = None;

        // Try to find a preferred free preg
        for preg in self.mach_env.preferred_regs_by_class[class as usize].iter().copied() {
            if !blocked_pregs.contains(preg) {
                return Ok(preg);
            }
        }
        // Try to find a non-preferred free preg
        for preg in self.mach_env.non_preferred_regs_by_class[class as usize].iter().copied() {
            if !blocked_pregs.contains(preg) {
                return Ok(preg);
            }
        }
        // Try to find the least used preg
        let mut distance = 0;
        for preg in self.mach_env.preferred_regs_by_class[class as usize].iter().copied() {
            let last_use = self.preg_last_use[preg.index()];
            let InstRange(start, end) = self.current_block_inst_range;
            if !last_use.is_valid() || last_use < start || last_use > end {
                // The preg is not live
                return Ok(preg);
            }
            let d = self.current_inst.index() - last_use.index();
            if d > distance {
                preg_found = Some(preg);
                distance = distance;
            }
        }

        return if let Some(preg) = preg_found {
            Ok(preg)
        } else {
            Err(RegAllocError::TooManyLiveRegs)
        };
    }

    #[inline]
    fn block_branch_allocations(&mut self) -> Result<(), RegAllocError> {
        // We need to find allocations for the target blocks.
        // Therefore, we need to determine the needed registers for
        // the jump instructions of the predecessors of the target blocks.
        // Generate the allocations for the block parameters
        let last_inst = self.func.block_insns(self.current_block).last();
        let succs = self.func.block_succs(self.current_block);
        if let Some(&succ) = succs.first() {
            let offset = self.blockparam_allocation_offsets[succ.index()];
            if self.blockparam_allocations[offset].is_some() {
                // We already have the allocations for the block parameters
                return Ok(());
            }
        } else {
            // The block has no successors
            return Ok(());
        }
        // The fixed regsets used in the jump instructions of the source block for each target block
        // We expect up to 2 target blocks for this jump instruction (we spill if more)
        let mut fixed_used_pregs = PRegSet::empty();

        for &target in succs {
            fixed_used_pregs.union_from(self.blocked_for_args(target)?);
        }

        for (idx, &target) in succs.iter().enumerate() {
            let params = self.func.branch_blockparams(target, last_inst, idx);
            let offset = self.blockparam_allocation_offsets[target.index()];
            for (param_idx, &param) in params.iter().enumerate() {
                let offset = offset + param_idx;
                let vreg_allocation = self.vreg_allocations[param.vreg()];
                if let Some(preg) = vreg_allocation.as_reg() {
                    if !fixed_used_pregs.contains(preg) {
                        // We found a preg for the block parameter
                        self.blockparam_allocations[offset] = Allocation::reg(preg);
                        fixed_used_pregs.add(preg);
                        continue;
                    }
                }
                let preg = self.find_preg_candidate(param.class(), fixed_used_pregs)?;
                // We found a preg for the block parameter
                self.blockparam_allocations[offset] = Allocation::reg(preg);
            }
        }

        Ok(())
    }

    #[inline]
    fn blocked_for_args(
        &mut self,
        block: Block,
    ) -> Result<PRegSet, RegAllocError> {
        let mut fixed_regs = SmallVec::new();
        let mut fixed_reg_set = PRegSet::empty(); // Cant be used for args at all.
        let mut free_regs = 0;
        for &pred in self.func.block_preds(block) {
            let inst = self.func.block_insns(pred).last();
            let operands = self.func.inst_operands(inst);
            let mut this_fixed_regs = 0; // Fixed reg count set.
            let mut this_free_regs = 0; // Free reg count needed.
            for operand in operands {
                if let OperandConstraint::FixedReg(preg) = operand.constraint() {
                    if !fixed_reg_set.contains(preg) {
                        fixed_reg_set.add(preg);
                        fixed_regs.push(preg);
                        free_regs.saturating_sub(1); // We can use one less free reg.
                    }
                    // Fix this reg.
                    this_fixed_regs += 1;
                }
                if let OperandConstraint::Reg = operand.constraint() {
                    this_free_regs += 1;
                }
            }

            let unused_fixed_regs = fixed_regs.len() as u32 - this_fixed_regs;
            if unused_fixed_regs >= this_free_regs {
                // We already have enough free fixed regs to cover the free regs.
                continue;
            }

            // We need more free regs.
            let additional_needed_free_regs = this_free_regs - unused_fixed_regs;
            free_regs += additional_needed_free_regs;
        }

        Ok(fixed_reg_set)
    }

    #[inline]
    fn handle_branch(
        &mut self,
        block: Block,
        inst: Inst,
        reserved_reg_set: &mut PRegSet,
    ) -> Result<(), RegAllocError> {
        if !self.func.is_branch(inst) {
            return Ok(())
        }

        if self.func.block_insns(block).last() != inst {
            // The branch is not the last instruction in the block
            // this is not supported
            return Err(RegAllocError::Branch(inst));
        }

        // Allocate arguments for the branch
        let mut scratch = [None; 3];
        for (idx, &successor) in self.func.block_succs(block).iter().enumerate() {
            let params = self.func.block_params(successor);
            let args = self.func.branch_blockparams(block, inst, idx);
            if params.len() != args.len() {
                return Err(RegAllocError::Branch(inst));
            }

            // Block parameters are always live-in
            // Allocate the stack slot for the parameter
            // Move the vreg to the stack slot
            for (&param, &arg) in params.iter().zip(args.iter()) {
                if param.class() != arg.class() {
                    return Err(RegAllocError::Branch(inst));
                }

                if scratch[param.class() as usize].is_none() {
                    scratch[param.class() as usize] = Some(self.find_scratch_reg(reserved_reg_set, param.class())?);
                }
                let scratch = Allocation::reg(scratch[param.class() as usize].unwrap());
                let allocation_in = Allocation::stack(self.vreg_find_spillslot(arg)
                    .ok_or(RegAllocError::EntryLivein)?);
                let allocation_out = Allocation::stack(self.vreg_get_spillslot(param));
                self.edits.push((ProgPoint::new(inst, InstPosition::Before), Edit::Move {
                    from: allocation_in,
                    to: scratch,
                }));
                self.edits.push((ProgPoint::new(inst, InstPosition::Before), Edit::Move {
                    from: scratch,
                    to: allocation_out,
                }));
            }
        }

        Ok(())
    }

    #[inline]
    fn find_scratch_reg(
        &self,
        reserved_reg_set: &PRegSet,
        reg_class: RegClass,
    ) -> Result<PReg, RegAllocError> {
        if let Some(preg) = self.mach_env.scratch_by_class[reg_class as usize] {
            if !reserved_reg_set.contains(preg) {
                return Ok(preg);
            }
        }

        self.allocate_preg(reg_class, reserved_reg_set)
    }

    #[inline]
    fn allocate_operands(&mut self) -> Result<(), RegAllocError> {
        // The offset of the instruction in the allocation array
        let offset = self.inst_alloc_offsets[self.current_inst.index()] as usize;
        let operands = self.func.inst_operands(self.current_inst);
        let mut allocated_pregs = PRegSet::empty();
        // Start by allocating the fixed registers
        for (i, operand) in operands.iter().enumerate() {
            if let OperandConstraint::FixedReg(preg) = operand.constraint() {
                let allocation = Allocation::reg(preg);
                allocated_pregs.add(preg);
                self.allocs[offset + i] = allocation;
            }
        }

        // Allocate the remaining registers
        for (i, operand) in operands.iter().enumerate() {
            if let OperandConstraint::Reg = operand.constraint() {
                let preg = self.find_preg_candidate(operand.class(), allocated_pregs)?;
                let allocation = Allocation::reg(preg);
                allocated_pregs.add(preg);
                self.allocs[offset + i] = allocation;
            }
        }

        // Allocate the stack operands
        for (i, operand) in operands.iter().enumerate() {
            match operand.constraint() {
                OperandConstraint::Any | OperandConstraint::Stack => {
                    if operand.constraint() == OperandConstraint::Any {
                        if let Some(preg) = self.find_preg_candidate(operand.class(), allocated_pregs).ok() {
                            let allocation = Allocation::reg(preg);
                            allocated_pregs.add(preg);
                            self.allocs[offset + i] = allocation;
                            continue;
                        }
                    }
                    let spill_slot = match operand.kind() {
                        // Allocate or find the stack slot if the operand is a def
                        OperandKind::Def => self.vreg_get_spillslot(operand.vreg()),
                        // Find the stack slot if the operand is a use (it must be live-in)
                        OperandKind::Use => self.vreg_find_spillslot(operand.vreg())
                            .ok_or(RegAllocError::EntryLivein)?,
                    };
                    self.allocs[offset + i] = Allocation::stack(spill_slot);
                }
                _ => {}
            }
        }

        // Resolve the reuse constraints (now that we have all the allocations)
        for (i, operand) in operands.iter().enumerate() {
            if let OperandConstraint::Reuse(idx) = operand.constraint() {
                self.allocs[offset + i] = self.allocs[offset + idx];
            }
        }

        // Insert the moves
        for (i, operand) in operands.iter().enumerate() {
            // If the operand is a fixed register that is live-in, we don't need to insert a move
            if operand.vreg().vreg() == VReg::MAX {
                continue;
            }

            // The allocation for the operand
            let allocation = self.allocs[offset + i];
            let edit = match operand.kind() {
                OperandKind::Def => {
                    (
                        ProgPoint::new(inst, InstPosition::After),
                        Edit::Move {
                            from: allocation,
                            // If the operand is a def, we can create a new stack slot if needed
                            to: Allocation::stack(self.vreg_get_spillslot(operand.vreg())),
                        }
                    )
                }
                OperandKind::Use => {
                    (
                        ProgPoint::new(inst, InstPosition::Before),
                        Edit::Move {
                            // If the operand is a use, we can't create a new stack slot
                            // since the stack slot must be live-in
                            from: Allocation::stack(self.vreg_find_spillslot(operand.vreg())
                                .ok_or(RegAllocError::EntryLivein)?),
                            to: allocation,
                        }
                    )
                }
            };
            self.edits.push(edit);
        }

        Ok(())
    }

    #[inline]
    fn allocate_preg(
        &self,
        class: RegClass,
        reserved_reg_set: &PRegSet,
    ) -> Result<PReg, RegAllocError> {
        let mut preg_found = None;
        // Try to find a preferred register
        for preg in self.mach_env.preferred_regs_by_class[class as usize].iter().copied() {
            if !reserved_reg_set.contains(preg) {
                preg_found = Some(preg);
                break;
            }
        }
        if preg_found.is_none() {
            // Try to find a non-preferred register
            for preg in self.mach_env.non_preferred_regs_by_class[class as usize].iter().copied() {
                if !reserved_reg_set.contains(preg) {
                    preg_found = Some(preg);
                    break;
                }
            }
        }

        if let Some(preg) = preg_found {
            Ok(preg)
        } else {
            Err(RegAllocError::TooManyLiveRegs)
        }
    }

    fn get_alloc(&self, instruction: Inst, index: usize) -> Allocation {
        self.allocs[self.inst_alloc_offsets[instruction.index()] as usize + index]
    }

    #[inline]
    fn vreg_find_spillslot(&mut self, vreg: VReg) -> Option<SpillSlot> {
        let index = vreg.vreg();
        let slot = self.spill_slots[index];
        if slot.is_valid() {
            return Some(slot);
        }

        None
    }

    #[inline]
    fn vreg_get_spillslot(&mut self, vreg: VReg) -> SpillSlot {
        if let Some(slot) = self.vreg_find_spillslot(vreg) {
            return slot;
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

        let slot = SpillSlot::new(slot as usize);
        self.spill_slots[vreg.vreg()] = slot;
        slot
    }
}


/// This allocator has no safety checks and assumes that the input is valid
/// It will produce invalid output if the input is invalid
///
/// The allocator is spilling heavyly and is not optimized for performance
/// but rather for compile time and simplicity (debugging builds, just-in-time compilation, etc.)
/// Hot paths should use a different allocator.
pub fn run<F: Function>(
    func: &F,
    mach_env: &MachineEnv,
) -> Result<Output, RegAllocError> {
    let env = Env::new(func, mach_env);

    env.run()
}

#[cfg(test)]
mod tests {
    use crate::RegClass;

    use super::*;

    #[test]
    fn test_debug_locations() {
        let vreg_0 = VReg::new(0, RegClass::Float);
        let vreg_1 = VReg::new(1, RegClass::Float);
        let debug_locations = [
            (vreg_0, Inst::new(15), Inst::new(40), 0),
            (vreg_0, Inst::new(80), Inst::new(100), 1),
            (vreg_1, Inst::new(30), Inst::new(40), 2),
            (vreg_1, Inst::new(50), Inst::new(90), 3),
        ];
        // vreg_0: 15 - 40 (0), 80 - 100 (1)
        // vreg_1: 30 - 40 (2), 50 - 90 (3)
        let debug_locations = debug_locations.as_slice();
        let mut debug_locations = DebugLocations::new(debug_locations);
        debug_locations.insert(vreg_0, ProgPoint::new(Inst::new(10), InstPosition::Before), Allocation::stack(SpillSlot::new(0)));
        debug_locations.insert(vreg_1, ProgPoint::new(Inst::new(10), InstPosition::Before), Allocation::stack(SpillSlot::new(1)));
        debug_locations.insert(vreg_0, ProgPoint::new(Inst::new(20), InstPosition::Before), Allocation::none()); // 10 - 20 : 0
        debug_locations.insert(vreg_1, ProgPoint::new(Inst::new(20), InstPosition::Before), Allocation::stack(SpillSlot::new(0))); // 10 - 20 : 1
        debug_locations.insert(vreg_0, ProgPoint::new(Inst::new(30), InstPosition::Before), Allocation::stack(SpillSlot::new(1)));
        debug_locations.insert(vreg_0, ProgPoint::new(Inst::new(40), InstPosition::Before), Allocation::stack(SpillSlot::new(0))); // 30 - 40 : 1
        debug_locations.insert(vreg_1, ProgPoint::new(Inst::new(40), InstPosition::Before), Allocation::stack(SpillSlot::new(1))); // 20 - 40 : 0
        debug_locations.insert(vreg_0, ProgPoint::new(Inst::new(50), InstPosition::Before), Allocation::none()); // 40 - 50 : 0
        debug_locations.insert(vreg_1, ProgPoint::new(Inst::new(60), InstPosition::Before), Allocation::none()); // 40 - 60 : 1
        // vreg_0: 10 - 20 (0), 30 - 40 (1), 40 - 50 (0)
        // vreg_1: 10 - 20 (1), 20 - 40 (0), 40 - 60 (1)

        let debug_locations = debug_locations.get_debug_locations(Inst::new(100));
        assert_eq!(debug_locations, vec![
            (0, ProgPoint::new(Inst::new(15), InstPosition::Before), ProgPoint::new(Inst::new(20), InstPosition::Before), Allocation::stack(SpillSlot::new(0))),
            (0, ProgPoint::new(Inst::new(30), InstPosition::Before), ProgPoint::new(Inst::new(40), InstPosition::Before), Allocation::stack(SpillSlot::new(1))),

            (2, ProgPoint::new(Inst::new(30), InstPosition::Before), ProgPoint::new(Inst::new(40), InstPosition::Before), Allocation::stack(SpillSlot::new(0))),
            (3, ProgPoint::new(Inst::new(50), InstPosition::Before), ProgPoint::new(Inst::new(60), InstPosition::Before), Allocation::stack(SpillSlot::new(1))),
        ]);
    }
}
