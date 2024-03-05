use std::prelude::rust_2015::Vec;
use std::vec;
use crate::{Allocation, Function, HwRegSet, Inst, MachineEnv, PReg, RegClass, SpillSlot, VReg};

#[derive(Clone, Copy)]
struct PRegAlloc {
    vreg: VReg,
    last_use: Inst,
}

pub struct AllocationState<'a, F: Function> {
    func: &'a F,
    mach_env: &'a MachineEnv,
    // Preffered registers
    pub preferred_regs_by_class: [HwRegSet; 3],
    pub non_preferred_regs_by_class: [HwRegSet; 3],
    // Spill slots
    num_spillslots: u32,
    free_spillslots_per_class: [Vec<SpillSlot>; 3],
    spillslot_allocations: Vec<VReg>,
    // PRegs
    register_state: HwRegSet,
    preg_allocations: [PRegAlloc; PReg::MAX],
    // VRegs
    vreg_allocations: Vec<Allocation>,
}

impl<'a, F: Function> AllocationState<'a, F> {
    #[inline]
    pub fn new(func: &'a F, mach_env: &'a MachineEnv) -> Self {
        let mut preferred_regs_by_class = [HwRegSet::empty(); 3];
        for reg_class in [RegClass::Int, RegClass::Float, RegClass::Vector] {
            for &preg in mach_env.preferred_regs_by_class[reg_class as usize].iter() {
                preferred_regs_by_class[reg_class as usize].add(preg);
            }
        }
        let mut non_preferred_regs_by_class = [HwRegSet::empty(); 3];
        for reg_class in [RegClass::Int, RegClass::Float, RegClass::Vector] {
            for &preg in mach_env.non_preferred_regs_by_class[reg_class as usize].iter() {
                non_preferred_regs_by_class[reg_class as usize].add(preg);
            }
        }
        let free_spillslots_per_class = [
            Vec::with_capacity(64),
            Vec::with_capacity(64),
            Vec::with_capacity(64),
        ];
        let spillslot_allocations = vec![VReg::invalid(); 64];
        let preg_allocations = [PRegAlloc {
            vreg: VReg::invalid(),
            last_use: Inst::invalid(),
        }; PReg::MAX];
        let vreg_allocations = vec![Allocation::none(); func.num_vregs()];

        Self {
            func,
            mach_env,
            preferred_regs_by_class,
            non_preferred_regs_by_class,
            num_spillslots: 0,
            free_spillslots_per_class,
            spillslot_allocations,
            register_state: HwRegSet::empty(),
            preg_allocations,
            vreg_allocations,
        }
    }

    #[inline]
    pub fn allocate_vreg(&mut self, instruction: Inst, vreg: VReg, allocation: Allocation) {
        if let Some(preg) = allocation.as_reg() {
            let index = preg.hw_enc();
            self.register_state.add(preg);
            self.preg_allocations[index].vreg = vreg;
            self.preg_allocations[index].last_use = instruction;
            self.vreg_allocations[vreg.vreg()] = allocation;
            return;
        }
        if let Some(spillslot) = allocation.as_stack() {
            let last = self.free_spillslots_per_class[vreg.class() as usize].last();
            if let Some(last) = last {
                if *last == spillslot {
                    self.free_spillslots_per_class[vreg.class() as usize].pop();
                }
            }
            debug_assert!(
                !self.free_spillslots_per_class[vreg.class() as usize].contains(&spillslot),
                "Spill slot should not be in the free list"
            );
            let index = spillslot.index();
            self.spillslot_allocations[index] = vreg;
            self.vreg_allocations[vreg.vreg()] = allocation;
            return;
        }
        if allocation.is_none() {
            let old_allocation = self.vreg_allocations[vreg.vreg()];
            self.vreg_allocations[vreg.vreg()] = allocation;
            if let Some(preg) = old_allocation.as_reg() {
                let index = preg.hw_enc();
                self.register_state.remove(preg);
                self.preg_allocations[index].vreg = VReg::invalid();
                self.preg_allocations[index].last_use = Inst::invalid();
                return;
            }
            if let Some(spillslot) = old_allocation.as_stack() {
                let index = spillslot.index();
                self.spillslot_allocations[index] = VReg::invalid();
                self.free_spillslots_per_class[vreg.class() as usize].push(spillslot);
                return;
            }
        }
    }

    #[inline]
    pub fn find_free_preg(&self, reg_class: RegClass, ignore_regs: HwRegSet) -> Option<PReg> {
        let mut free_regs = self.preferred_regs_by_class[reg_class as usize];
        free_regs = free_regs & !ignore_regs; // Remove ignore_regs
        free_regs = free_regs & !self.register_state; // Remove used_regs
        if let Some(preg) = free_regs.into_iter().next() {
            return Some(PReg::new(preg, reg_class));
        }

        let mut free_regs = self.non_preferred_regs_by_class[reg_class as usize];
        free_regs = free_regs & !ignore_regs; // Remove ignore_regs
        free_regs = free_regs & !self.register_state; // Remove used_regs

        free_regs.into_iter().next().map(|preg| PReg::new(preg, reg_class))
    }

    #[inline]
    pub fn find_furthest_used_preg(&self, reg_class: RegClass, ignore_regs: HwRegSet) -> Option<PReg> {
        let mut furthest_use = Inst::new(0);
        let mut furthest_use_preg = PReg::invalid();
        for pregs in [
            &self.mach_env.non_preferred_regs_by_class[reg_class as usize],
            &self.mach_env.preferred_regs_by_class[reg_class as usize],
        ] {
            for &preg in pregs.iter().rev() {
                if ignore_regs.contains(preg) {
                    continue;
                }
                if self.register_state.contains(preg) {
                    let index = preg.hw_enc();
                    if self.preg_allocations[index].last_use >= furthest_use {
                        furthest_use = self.preg_allocations[index].last_use;
                        furthest_use_preg = preg;
                    }
                }
            }
        }

        if furthest_use_preg.hw_enc() != PReg::MAX {
            return Some(furthest_use_preg);
        }

        None
    }

    #[inline]
    pub fn find_free_spillslot(&self, reg_class: RegClass) -> Option<SpillSlot> {
        let spillslots = &self.free_spillslots_per_class[reg_class as usize];

        if let Some(spillslot) = spillslots.last() {
            return Some(*spillslot);
        }

        None
    }

    #[inline]
    pub fn allocate_spillslot(&mut self, vreg: VReg) -> SpillSlot {
        if let Some(spillslot) = self.find_free_spillslot(vreg.class()) {
            return spillslot;
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
    pub fn free_allocation(&mut self, vreg: VReg) -> Allocation {
        let allocation = self.vreg_allocations[vreg.vreg()];
        self.allocate_vreg(Inst::invalid(), vreg, Allocation::none());

        allocation
    }

    #[inline]
    pub fn find_scratch_reg(
        &self,
        reg_class: RegClass,
        ignore_regs: HwRegSet,
    ) -> Option<PReg> {
        if let Some(preg) = self.mach_env.scratch_by_class[reg_class as usize] {
            if !ignore_regs.contains(preg) {
                return Some(preg);
            }
        }

        if let Some(preg) = self.find_free_preg(reg_class, ignore_regs) {
            return Some(preg);
        }

        None
    }

    #[inline]
    pub fn get_vreg_allocation(&self, vreg: VReg) -> Allocation {
        self.vreg_allocations[vreg.vreg()]
    }

    #[inline]
    pub fn get_preg_vreg(&self, preg: PReg) -> Option<VReg> {
        if self.register_state.contains(preg) {
            let index = preg.hw_enc();
            let vreg = self.preg_allocations[index].vreg;

            if vreg.class() == preg.class() {
                return Some(vreg);
            }
        }

        None
    }

    #[inline]
    pub fn num_spillslots(&self) -> usize {
        self.num_spillslots as usize
    }
}