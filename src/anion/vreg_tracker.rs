use std::vec;
use std::vec::Vec;
use crate::{Allocation, Function, VReg};

pub struct VRegTracker {
    vreg_allocations: Vec<Allocation>,
}

impl VRegTracker {
    #[inline]
    pub fn new<F: Function>(func: &F) -> Self {
        Self {
            vreg_allocations: vec![Allocation::none(); func.num_vregs()],
        }
    }

    #[inline]
    pub fn get(&self, vreg: VReg) -> Option<Allocation> {
        if vreg.vreg() >= self.vreg_allocations.len() {
            return None;
        }

        let allocation = self.vreg_allocations[vreg.vreg()];

        if allocation.is_none() {
            None
        } else {
            Some(allocation)
        }
    }

    #[inline]
    pub fn set(&mut self, vreg: VReg, allocation: Allocation) {
        debug_assert!(vreg.vreg() < self.vreg_allocations.len());
        self.vreg_allocations[vreg.vreg()] = allocation;
    }
}