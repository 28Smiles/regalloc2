use std::vec::Vec;
use std::vec;

pub struct OffsetVec<T> {
    offsets: Vec<u32>,
    data: Vec<T>,
}

impl<T: Default + Clone> OffsetVec<T> {
    #[inline]
    pub fn new(size_iter: impl Iterator<Item = u32>) -> Self {
        let mut data = 0;
        let mut offsets = Vec::with_capacity(size_iter.size_hint().0 + 1);
        offsets.push(data);
        for size in size_iter {
            data += size;
            offsets.push(data);
        }

        Self {
            offsets,
            data: vec![T::default(); data as usize],
        }
    }

    #[inline]
    pub fn set(&mut self, x: u32, y: u32, value: T) {
        debug_assert!(x < self.offsets.len() as u32);
        let offset = self.offsets[x as usize] as usize;
        self.data[offset + y as usize] = value;
    }

    #[inline]
    pub fn get(&self, x: u32, y: u32) -> &T {
        debug_assert!(x < self.offsets.len() as u32);
        let offset = self.offsets[x as usize] as usize;
        &self.data[offset + y as usize]
    }

    #[inline]
    pub fn get_mut(&mut self, x: u32, y: u32) -> &mut T {
        debug_assert!(x < self.offsets.len() as u32);
        let offset = self.offsets[x as usize] as usize;
        &mut self.data[offset + y as usize]
    }

    #[inline]
    pub fn set_all(&mut self, x: u32, value: &[T]) {
        debug_assert!(x < self.offsets.len() as u32);
        let offset = self.offsets[x as usize] as usize;
        let len = self.offsets[x as usize + 1] as usize - offset;
        debug_assert_eq!(len, value.len());
        for (i, value) in value.iter().enumerate() {
            self.data[offset + i] = value.clone();
        }
    }

    #[inline]
    pub fn get_all(&self, x: u32) -> &[T] {
        debug_assert!(x < self.offsets.len() as u32);
        let offset = self.offsets[x as usize] as usize;
        let len = self.offsets[x as usize + 1] as usize - offset;
        &self.data[offset..offset + len]
    }

    #[inline]
    pub fn get_all_mut(&mut self, x: u32) -> &mut [T] {
        debug_assert!(x < self.offsets.len() as u32);
        let offset = self.offsets[x as usize] as usize;
        let len = self.offsets[x as usize + 1] as usize - offset;
        &mut self.data[offset..offset + len]
    }

    #[inline]
    pub fn into_inner(self) -> (Vec<u32>, Vec<T>) {
        (self.offsets, self.data)
    }
}