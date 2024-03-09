use std::vec::Vec;
use std::vec;
use crate::{Function, RegClass, SpillSlot, VReg};

pub struct SpillSlotState<'a, F> {
    func: &'a F,
    num_spillslots: u32,
    free_spillslots_per_class: [Vec<SpillSlot>; 3],
    spillslot_allocations: Vec<VReg>,
}

impl<'a, F: Function> SpillSlotState<'a, F> {
    #[inline]
    pub fn new(func: &'a F) -> Self {
        let free_spillslots_per_class = [
            Vec::with_capacity(64),
            Vec::with_capacity(64),
            Vec::with_capacity(64),
        ];
        let spillslot_allocations = vec![VReg::invalid(); 64];

        Self {
            func,
            num_spillslots: 0,
            free_spillslots_per_class,
            spillslot_allocations,
        }
    }

    #[inline(always)]
    pub fn deallocate(&mut self, spillslot: SpillSlot) {
        debug_assert!(spillslot.index() < self.spillslot_allocations.len());
        let vreg = self.spillslot_allocations[spillslot.index()];
        debug_assert_eq!(vreg, VReg::invalid());
        self.spillslot_allocations[spillslot.index()] = VReg::invalid();
        self.free_spillslots_per_class[vreg.class() as usize].push(spillslot);
    }

    #[inline(always)]
    pub fn allocate(&mut self, vreg: VReg, spillslot: SpillSlot) {
        debug_assert!(spillslot.index() < self.spillslot_allocations.len());
        debug_assert!(self.spillslot_allocations[spillslot.index()] == VReg::invalid());
        self.spillslot_allocations[spillslot.index()] = vreg;
    }

    #[inline(always)]
    pub fn find(&self, spillslot: SpillSlot) -> Option<VReg> {
        debug_assert!(spillslot.index() < self.spillslot_allocations.len());
        let vreg = self.spillslot_allocations[spillslot.index()];

        if vreg != VReg::invalid() {
            Some(vreg)
        } else {
            None
        }
    }

    #[inline(always)]
    fn find_free(&mut self, reg_class: RegClass) -> Option<SpillSlot> {
        self.free_spillslots_per_class[reg_class as usize].pop()
    }

    #[inline]
    pub fn reserve(&mut self, reg_class: RegClass) -> SpillSlot {
        if let Some(spillslot) = self.find_free(reg_class) {
            return spillslot;
        }

        let size = self.func.spillslot_size(reg_class) as u32;
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
    pub fn num_spillslots(&self) -> u32 {
        self.num_spillslots
    }
}