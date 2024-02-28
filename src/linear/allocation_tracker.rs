use std::cmp::Ordering;
use std::collections::{BinaryHeap, BTreeSet};
use std::vec;
use std::vec::Vec;

use crate::{Allocation, Inst, MachineEnv, PReg, RegAllocError, RegClass, SpillSlot, VReg};
use crate::linear::usage_tracker::UsageTracker;

#[derive(Copy, Clone)]
struct PregAllocation {
    /// The virtual register that currently occupies this preg.
    vreg: VReg,
    /// The instruction this register was last modified at.
    last_modified: Inst,
    /// Is stack slot.
    is_stack: bool,
    /// Is preferred.
    is_preferred: [bool; 3],
    /// Is non-preferred.
    is_non_preferred: [bool; 3],
}

impl PregAllocation {
    #[inline]
    fn new() -> Self {
        Self {
            vreg: VReg::invalid(),
            last_modified: Inst::invalid(),
            is_stack: false,
            is_preferred: [false; 3],
            is_non_preferred: [false; 3],
        }
    }

    #[inline]
    fn is_free(&self) -> bool {
        self.vreg == VReg::invalid()
    }

    #[inline]
    fn instructions_ago(&self, inst: Inst) -> usize {
        inst.index() - self.last_modified.index()
    }
}

pub struct AllocationTracker {
    /// Mapping from virtual registers to their current allocation.
    vreg_allocations: Vec<Allocation>,
    /// Mapping from physical registers to their current allocation.
    preg_allocations: Vec<PregAllocation>,
    // -------------------------
    // The following fields are used to track the free and filled registers and spill slots.
    // -------------------------
    /// A list of preferred registers for each register class.
    free_preferred_regs_by_class: [BTreeSet<usize>; 3],
    filled_preferred_regs_by_class: [BTreeSet<usize>; 3],
    /// A list of non-preferred registers for each register class.
    free_non_preferred_regs_by_class: [BTreeSet<usize>; 3],
    filled_non_preferred_regs_by_class: [BTreeSet<usize>; 3],
    /// A list of free spill slots.
    free_spill_slots: Vec<SpillSlot>,
    /// The next spill slot to allocate.
    next_spill_slot: usize,
}

impl AllocationTracker {
    #[inline]
    pub fn new(
        machine_env: &MachineEnv,
    ) -> Self {
        let vreg_allocations = vec![Allocation::none(); VReg::MAX];
        let mut preg_allocations = vec![PregAllocation::new(); PReg::MAX];

        for preg in machine_env.fixed_stack_slots.iter().copied() {
            preg_allocations[preg.hw_enc()].is_stack = true;
        }

        for i in 0..3 {
            for preg in machine_env.preferred_regs_by_class[i].iter().copied() {
                preg_allocations[preg.hw_enc()].is_preferred[i] = true;
            }
            for preg in machine_env.non_preferred_regs_by_class[i].iter().copied() {
                preg_allocations[preg.hw_enc()].is_non_preferred[i] = true;
            }
        }

        // For the physical registers we only use the hw_enc, since we can't use
        // the hardware register twice anyway.
        let free_preferred_regs_by_class = [
            machine_env.preferred_regs_by_class[0].iter().map(|preg| preg.hw_enc()).collect(),
            machine_env.preferred_regs_by_class[1].iter().map(|preg| preg.hw_enc()).collect(),
            machine_env.preferred_regs_by_class[2].iter().map(|preg| preg.hw_enc()).collect(),
        ];
        let filled_preferred_regs_by_class = [
            BTreeSet::new(),
            BTreeSet::new(),
            BTreeSet::new(),
        ];

        let free_non_preferred_regs_by_class = [
            machine_env.non_preferred_regs_by_class[0].iter().map(|preg| preg.hw_enc()).collect(),
            machine_env.non_preferred_regs_by_class[1].iter().map(|preg| preg.hw_enc()).collect(),
            machine_env.non_preferred_regs_by_class[2].iter().map(|preg| preg.hw_enc()).collect(),
        ];
        let filled_non_preferred_regs_by_class = [
            BTreeSet::new(),
            BTreeSet::new(),
            BTreeSet::new(),
        ];

        Self {
            vreg_allocations,
            preg_allocations,
            free_preferred_regs_by_class,
            filled_preferred_regs_by_class,
            free_non_preferred_regs_by_class,
            filled_non_preferred_regs_by_class,
            free_spill_slots: Vec::with_capacity(32),
            next_spill_slot: 0,
        }
    }

    #[inline]
    pub fn allocation(&self, vreg: VReg) -> Allocation {
        self.vreg_allocations[vreg.vreg()]
    }

    #[inline]
    pub fn preg(&self, vreg: VReg) -> Option<PReg> {
        self.allocation(vreg).as_reg()
    }

    #[inline]
    pub fn vreg(&self, preg: PReg) -> VReg {
        self.preg_allocations[preg.index()].vreg
    }

    #[inline]
    pub fn find_free_preferred(
        &self,
        reg_class: RegClass,
        blocked_hw_regs: &BTreeSet<usize>,
    ) -> Option<PReg> {
        self.free_preferred_regs_by_class[reg_class as usize]
            .iter()
            .copied()
            .filter(|&preg| !blocked_hw_regs.contains(&preg))
            .next()
            .map(|hw_enc| PReg::new(hw_enc, reg_class))
    }

    #[inline]
    pub fn find_free_non_preferred(
        &self,
        reg_class: RegClass,
        blocked_hw_regs: &BTreeSet<usize>,
    ) -> Option<PReg> {
        self.free_non_preferred_regs_by_class[reg_class as usize]
            .iter()
            .copied()
            .filter(|&preg| !blocked_hw_regs.contains(&preg))
            .next()
            .map(|hw_enc| PReg::new(hw_enc, reg_class))
    }

    #[inline]
    pub fn find_free(
        &self,
        reg_class: RegClass,
        blocked_hw_regs: &BTreeSet<usize>,
    ) -> Option<PReg> {
        self.find_free_preferred(reg_class, blocked_hw_regs)
            .or_else(|| self.find_free_non_preferred(reg_class, blocked_hw_regs))
    }

    #[inline]
    pub fn find_freeable(
        &self,
        inst: Inst,
        reg_class: RegClass,
        blocked: &BTreeSet<usize>,
        usage_tracker: &mut UsageTracker,
    ) -> Result<PReg, RegAllocError> {
        self.filled_preferred_regs_by_class[reg_class as usize]
            .iter()
            .chain(self.filled_non_preferred_regs_by_class[reg_class as usize].iter())
            .filter(|&preg| !blocked.contains(preg))
            .map(|&preg| (preg, self.preg_allocations[preg].instructions_ago(
                    usage_tracker.next_usage(inst, self.preg_allocations[preg].vreg)
                    .map(|progpoint| progpoint.inst())
                    .unwrap_or(inst)
            )))
            .max_by(|(_, a), (_, b)| a.cmp(b))
            .map(|(preg, _)| PReg::new(preg, reg_class))
            .ok_or(RegAllocError::TooManyLiveRegs)
    }

    #[inline]
    pub fn free(&mut self, vreg: VReg) -> Allocation {
        let idx = vreg.vreg();
        // We find and free the allocation of the virtual register.
        let allocation = self.vreg_allocations[idx];
        self.vreg_allocations[idx] = Allocation::none();
        // Next we update the physical register allocation,
        // if the virtual register was allocated to a physical register.
        if let Some(preg) = allocation.as_reg() {
            // If the virtual register was allocated to a physical register then free it.
            let preg_allocation = &mut self.preg_allocations[preg.hw_enc()];
            preg_allocation.vreg = VReg::invalid();
            // We also need to update the free and filled register lists.
            // Since we stored the preferred and non-preferred registers in the preg_allocation
            // we can use that to only update the correct lists, instead of
            // checking whether the register is in the preferred or non-preferred list.
            for i in 0..3 {
                if preg_allocation.is_preferred[i] {
                    self.free_preferred_regs_by_class[i].insert(preg.hw_enc());
                    self.filled_preferred_regs_by_class[i].remove(&preg.hw_enc());
                } else if preg_allocation.is_non_preferred[i] {
                    self.free_non_preferred_regs_by_class[i].insert(preg.hw_enc());
                    self.filled_non_preferred_regs_by_class[i].remove(&preg.hw_enc());
                }
            }
        }
        if let Some(slot) = allocation.as_stack() {
            // If the virtual register was allocated to a stack slot then free it.
            self.free_spill_slots.push(slot);
        }


        allocation
    }

    #[inline]
    pub fn allocate_preg(&mut self, preg: PReg, vreg: VReg, inst: Inst) -> (Allocation, Option<VReg>) {
        let preg_allocation = &mut self.preg_allocations[preg.hw_enc()];

        // Check if the physical register is already allocated to a virtual register.
        let old_vreg = if preg_allocation.is_free() {
            None
        } else {
            let old_vreg = preg_allocation.vreg;
            self.vreg_allocations[old_vreg.vreg()] = Allocation::none();

            Some(old_vreg)
        };

        // We update the physical register allocation.
        preg_allocation.vreg = vreg;
        preg_allocation.last_modified = inst;

        // We also need to update the virtual register allocation.
        self.vreg_allocations[vreg.vreg()] = Allocation::reg(preg);

        // We also need to update the free and filled register lists.
        for i in 0..3 {
            if preg_allocation.is_preferred[i] {
                self.free_preferred_regs_by_class[i].remove(&preg.hw_enc());
                self.filled_preferred_regs_by_class[i].insert(preg.hw_enc());
            } else if preg_allocation.is_non_preferred[i] {
                self.free_non_preferred_regs_by_class[i].remove(&preg.hw_enc());
                self.filled_non_preferred_regs_by_class[i].insert(preg.hw_enc());
            }
        }

        (Allocation::reg(preg), old_vreg)
    }

    #[inline]
    pub fn allocate_stack(&mut self, vreg: VReg) -> Allocation {
        let spill_slot = if let Some(slot) = self.free_spill_slots.pop() {
            slot
        } else {
            let slot = self.next_spill_slot;
            self.next_spill_slot += 1;

            slot
        };

        let allocation = Allocation::stack(spill_slot);
        self.vreg_allocations[vreg.vreg()] = allocation;

        allocation
    }
}
