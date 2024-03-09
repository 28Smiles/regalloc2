use crate::{HwRegSet, Inst, MachineEnv, PReg, PRegSet, RegClass, VReg};

#[derive(Copy, Clone)]
pub struct PRegState<'a> {
    mach_env: &'a MachineEnv,
    stack_slots: PRegSet,
    regs: PRegSet,
    preferred_regs: PRegSet,
    non_preferred_regs: PRegSet,
    // State
    filled_regs: PRegSet,
    reg_allocations: [(VReg, Inst); PReg::NUM_INDEX],
}

impl<'a> PRegState<'a> {
    #[inline]
    pub fn new(mach_env: &'a MachineEnv) -> Self {
        let mut preferred_regs = PRegSet::empty();
        for reg_class in [RegClass::Int, RegClass::Float, RegClass::Vector] {
            for &preg in mach_env.preferred_regs_by_class[reg_class as usize].iter() {
                preferred_regs.add(preg);
            }
        }
        let mut non_preferred_regs = PRegSet::empty();
        for reg_class in [RegClass::Int, RegClass::Float, RegClass::Vector] {
            for &preg in mach_env.non_preferred_regs_by_class[reg_class as usize].iter() {
                non_preferred_regs.add(preg);
            }
        }
        let regs = preferred_regs | non_preferred_regs;
        let mut stack_slots = PRegSet::empty();
        for &preg in mach_env.fixed_stack_slots.iter() {
            stack_slots.add(preg);
        }

        Self {
            mach_env,
            stack_slots,
            regs,
            preferred_regs,
            non_preferred_regs,
            filled_regs: PRegSet::empty(),
            reg_allocations: [(VReg::invalid(), Inst::invalid()); PReg::NUM_INDEX],
        }
    }

    #[inline]
    pub fn is_available(&self, preg: PReg) -> bool {
        !self.filled_regs.contains(preg)
    }

    #[inline]
    pub fn allocate(&mut self, vreg: VReg, preg: PReg, inst: Inst) {
        debug_assert!(self.is_available(preg));
        self.filled_regs.add(preg);
        self.reg_allocations[preg.index()] = (vreg, inst);
    }

    #[inline]
    pub fn deallocate(&mut self, preg: PReg) {
        debug_assert!(self.filled_regs.contains(preg));
        self.filled_regs.remove(preg);
    }

    #[inline]
    pub fn find(&self, preg: PReg) -> Option<(VReg, Inst)> {
        if !self.filled_regs.contains(preg) {
            None
        } else {
            Some(self.reg_allocations[preg.index()])
        }
    }

    #[inline]
    pub fn find_free(&self, reg_class: RegClass, ignore: PRegSet) -> Option<PReg> {
        for free_regs in [
            self.preferred_regs.to_hw(reg_class) & !self.filled_regs.to_hw(reg_class) & !ignore.to_hw(reg_class),
            self.non_preferred_regs.to_hw(reg_class) & !self.filled_regs.to_hw(reg_class) & !ignore.to_hw(reg_class),
        ] {
            if let Some(hw_enc) = free_regs.into_iter().next() {
                return Some(PReg::new(hw_enc, reg_class));
            }
        }

        None
    }

    #[inline]
    pub fn find_furthest_use(&self, reg_class: RegClass, ignore: PRegSet) -> Option<PReg> {
        let mut furthest_use = Inst::invalid();
        let mut furthest_use_preg = PReg::invalid();
        for pregs in [
            &self.mach_env.non_preferred_regs_by_class[reg_class as usize],
            &self.mach_env.preferred_regs_by_class[reg_class as usize],
        ] {
            for &preg in pregs.iter().rev() {
                if self.filled_regs.contains(preg) && !ignore.contains(preg) {
                    let index = preg.index();
                    if self.reg_allocations[index].1 >= furthest_use {
                        furthest_use = self.reg_allocations[index].1;
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
    pub fn regs_by_class(&self, reg_class: RegClass) -> HwRegSet {
        self.regs.to_hw(reg_class)
    }

    #[inline]
    pub fn preferred_regs_by_class(&self, reg_class: RegClass) -> HwRegSet {
        self.preferred_regs.to_hw(reg_class)
    }

    #[inline]
    pub fn non_preferred_regs_by_class(&self, reg_class: RegClass) -> HwRegSet {
        self.non_preferred_regs.to_hw(reg_class)
    }

    #[inline]
    pub fn stack_slots(&self) -> PRegSet {
        self.stack_slots
    }
}