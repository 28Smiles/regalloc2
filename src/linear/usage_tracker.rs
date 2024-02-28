use std::vec;
use std::vec::Vec;
use smallvec::SmallVec;

use crate::{Function, Inst, InstPosition, OperandPos, ProgPoint, VReg};

pub struct UsageTracker {
    offsets: Vec<usize>,
    usages: Vec<ProgPoint>,
}

impl UsageTracker {
    #[inline]
    pub fn new<F: Function>(f: &F) -> UsageTracker {
        // Collect all uses of virtual registers in the function.
        // We store the uses in a vector of small vectors where the index is the virtual register.
        // The small vectors contain the program points where the virtual register is used.
        // We reserve space for up to 4 uses of each virtual register in the host vector.
        // For most virtual registers this is enough to avoid dynamic allocation.
        // Heavily used virtual registers exceed this limit and will cause dynamic allocation.
        let mut positions = 0;
        let mut usage_buckets = vec![
            SmallVec::<[ProgPoint; 4]>::new().capacity(); f.num_vregs()
        ];
        for inst in 0..f.num_insts() {
            let inst = Inst::new(inst);
            for operand in f.inst_operands(inst) {
                usage_buckets[operand.vreg().vreg()].push(ProgPoint::new(
                    inst,
                    match operand.pos() {
                        OperandPos::Early => InstPosition::Before,
                        OperandPos::Late => InstPosition::After,
                    }
                ));
                positions += 1;
            }
        }

        // We can now flatten the small vectors into a single vector and create an offset vector,
        // which will be used to quickly find the next use of a virtual register.
        let mut offsets = Vec::with_capacity(f.num_vregs() + 1);
        let mut usages = Vec::with_capacity(positions);

        offsets.push(0);
        for vreg_idx in 0..f.num_vregs() {
            let bucket = &usage_buckets[vreg_idx];
            offsets.push(offsets.last().unwrap() + bucket.len());
            usages.extend_from_slice(bucket);
        }

        UsageTracker { offsets, usages }
    }

    #[inline]
    pub fn next_usage(&mut self, instr: Inst, vreg: VReg) -> Option<ProgPoint> {
        let idx = vreg.vreg();
        let offset = self.offsets[idx];
        let end = self.offsets[idx + 1];
        // If the offset is equal to the end then there are no more uses of the virtual register.
        if end == offset {
            return None;
        }

        // We need to find the next use of the virtual register.
        for i in offset..end {
            let pp = self.usages[i];
            if pp.inst() > instr {
                // We found the next use of the virtual register.
                // We store the new offset to avoid searching from the beginning next time.
                self.offsets[idx] = i;

                return Some(pp);
            }
        }

        // There are no more uses of the virtual register.
        self.offsets[idx] = end;

        None
    }
}
