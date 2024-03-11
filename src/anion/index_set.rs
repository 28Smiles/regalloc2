use smallvec::{SmallVec, smallvec};

pub struct IndexSet(SmallVec<[u64; 4]>, usize);

impl IndexSet {
    #[inline]
    pub fn new(size: usize) -> Self {
        IndexSet(smallvec![0; size / 64 + 1], size)
    }

    #[inline]
    pub fn insert(&mut self, index: usize) {
        let (word, bit) = (index / 64, index % 64);
        self.0[word] |= 1 << bit;
    }

    #[inline]
    pub fn remove(&mut self, index: usize) {
        let (word, bit) = (index / 64, index % 64);
        self.0[word] &= !(1 << bit);
    }

    #[inline]
    pub fn contains(&self, index: usize) -> bool {
        let (word, bit) = (index / 64, index % 64);
        self.0[word] & (1 << bit) != 0
    }

    #[inline]
    pub fn clear(&mut self) {
        self.0.as_mut_slice().fill(0);
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.iter().all(|&x| x == 0)
    }

    #[inline]
    pub fn is_full(&self) -> bool {
        let len = self.0.len();
        self.0[..len - 1].iter().all(|&x| x == u64::MAX)
            && self.0[len - 1] == (1 << self.1 % 64) - 1
    }
}
