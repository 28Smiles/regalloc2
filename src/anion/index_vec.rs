use std::ops::Range;
use std::vec::Vec;
use std::vec;

#[derive(Debug, Clone)]
pub struct IndexVec<T> {
    indices: Vec<Range<usize>>,
    data: Vec<T>,
}

impl<T> IndexVec<T> {
    #[inline]
    pub fn new(index_capacity: usize) -> Self {
        Self {
            indices: vec![0..0; index_capacity],
            data: Vec::with_capacity(index_capacity),
        }
    }

    #[inline]
    pub fn new_with_capacity(index_capacity: usize, data_capacity: usize) -> Self {
        Self {
            indices: vec![0..0; index_capacity],
            data: Vec::with_capacity(data_capacity),
        }
    }

    #[inline]
    pub fn push(&mut self, index: usize, value: T) {
        debug_assert!(index < self.indices.len());
        let range = &mut self.indices[index];
        let current_len = self.data.len();
        self.data.push(value);
        if range.end == current_len {
            // We can just push the value
            range.end += 1;
        } else {
            debug_assert!(range.start == 0, "Index not contiguous");
            range.start = current_len;
            range.end = self.data.len();
        }
    }

    #[inline]
    pub fn extend(&mut self, index: usize, values: impl IntoIterator<Item = T>) {
        debug_assert!(index < self.indices.len());
        let range = &mut self.indices[index];
        let current_len = self.data.len();
        self.data.extend(values);
        if range.end == current_len {
            // We can just push the value
            range.end += self.data.len() - current_len;
        } else {
            debug_assert!(range.start == 0, "Index not contiguous");
            range.start = current_len;
            range.end = self.data.len();
        }
    }

    #[inline]
    pub fn get(&self, index: usize) -> &[T] {
        debug_assert!(index < self.indices.len());
        let range = self.indices[index].clone();
        debug_assert!(range.start <= range.end, "Invalid range");

        &self.data[range.clone()]
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> &mut [T] {
        debug_assert!(index < self.indices.len());
        let range = self.indices[index].clone();
        debug_assert!(range.start <= range.end, "Invalid range");

        &mut self.data[range.clone()]
    }

    #[inline]
    pub fn into_iter(self) -> IndexVecIntoIter<T> {
        let Self { indices, data } = self;
        let index = (0, indices.len());
        let data_index = (0, data.len());

        IndexVecIntoIter {
            indices,
            data,
            index,
            data_index,
        }
    }

    #[inline]
    pub fn into_iter_block_rev(self) -> IndexVecIntoIterBlockRev<T> {
        let Self { indices, data } = self;
        let data_index = data.len();

        IndexVecIntoIterBlockRev {
            indices,
            data,
            index: 0,
            data_index,
        }
    }
}

pub struct IndexVecIntoIter<T> {
    indices: Vec<Range<usize>>,
    data: Vec<T>,
    index: (usize, usize),
    data_index: (usize, usize),
}

impl<T> Iterator for IndexVecIntoIter<T> {
    type Item = (usize, T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.index.0 == self.index.1 {
                #[cold]
                fn cold_none<T>() -> Option<(usize, T)> {
                    None
                }

                return cold_none();
            }

            let range = &self.indices[self.index.0];
            if range.start == range.end {
                self.index.0 += 1;
                self.data_index.0 = 0;
                continue;
            }

            if self.data_index.0 >= range.end {
                self.index.0 += 1;
                self.data_index.0 = 0;
                continue;
            }

            if self.data_index.0 <= range.start {
                self.data_index.0 = range.start;
            }

            let data = unsafe {
                std::ptr::read(&self.data[self.data_index.0])
            };
            self.data_index.0 += 1;

            return Some((self.index.0, data));
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.data.len(), Some(self.data.len()))
    }
}

impl<T> DoubleEndedIterator for IndexVecIntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            if self.index.0 == self.index.1 {
                #[cold]
                fn cold_none<T>() -> Option<(usize, T)> {
                    None
                }

                return cold_none();
            }

            let range = &self.indices[self.index.1 - 1];
            if range.start == range.end {
                self.index.1 -= 1;
                self.data_index.1 = self.data.len();
                continue;
            }

            if self.data_index.1 > range.end {
                self.data_index.1 = range.end;
            }

            if self.data_index.1 == range.start {
                self.index.1 -= 1;
                self.data_index.1 = self.data.len();
                continue;
            }

            self.data_index.1 -= 1;

            let data = unsafe {
                std::ptr::read(&self.data[self.data_index.1])
            };

            return Some((self.index.1 - 1, data));
        }
    }
}


pub struct IndexVecIntoIterBlockRev<T> {
    indices: Vec<Range<usize>>,
    data: Vec<T>,
    index: usize,
    data_index: usize,
}

impl<T> Iterator for IndexVecIntoIterBlockRev<T> {
    type Item = (usize, T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.index == self.indices.len() {
                #[cold]
                fn cold_none<T>() -> Option<(usize, T)> {
                    None
                }

                return cold_none();
            }

            let range = &self.indices[self.index];
            if range.start == range.end {
                self.index += 1;
                self.data_index = self.data.len();
                continue;
            }

            if self.data_index > range.end {
                self.data_index = range.end;
            }

            if self.data_index == range.start {
                self.index += 1;
                self.data_index = self.data.len();
                continue;
            }

            self.data_index -= 1;

            let data = unsafe {
                std::ptr::read(&self.data[self.data_index])
            };

            return Some((self.index, data));
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.data.len(), Some(self.data.len()))
    }
}

#[cfg(test)]
mod tests {
    use std::println;
    use super::*;

    #[test]
    fn test_index_vec() {
        let mut index_vec = IndexVec::new(10);
        index_vec.push(0, 1);
        index_vec.push(0, 2);
        index_vec.push(2, 5);
        index_vec.push(2, 6);
        index_vec.push(1, 3);
        index_vec.push(1, 4);

        let mut iter = index_vec.into_iter();
        assert_eq!(iter.next(), Some((0, 1)));
        assert_eq!(iter.next(), Some((0, 2)));
        assert_eq!(iter.next(), Some((1, 3)));
        assert_eq!(iter.next(), Some((1, 4)));
        assert_eq!(iter.next(), Some((2, 5)));
        assert_eq!(iter.next(), Some((2, 6)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_index_vec_back() {
        let mut index_vec = IndexVec::new(10);
        index_vec.push(0, 1);
        index_vec.push(0, 2);
        index_vec.push(2, 5);
        index_vec.push(2, 6);
        index_vec.push(1, 3);
        index_vec.push(1, 4);
        println!("{:?}", index_vec);

        let mut iter = index_vec.into_iter().rev();
        assert_eq!(iter.next(), Some((2, 6)));
        assert_eq!(iter.next(), Some((2, 5)));
        assert_eq!(iter.next(), Some((1, 4)));
        assert_eq!(iter.next(), Some((1, 3)));
        assert_eq!(iter.next(), Some((0, 2)));
        assert_eq!(iter.next(), Some((0, 1)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_index_vec_block_rev() {
        let mut index_vec = IndexVec::new(10);
        index_vec.push(0, 1);
        index_vec.push(0, 2);
        index_vec.push(2, 5);
        index_vec.push(2, 6);
        index_vec.push(1, 3);
        index_vec.push(1, 4);
        println!("{:?}", index_vec);

        let mut iter = index_vec.into_iter_block_rev();
        assert_eq!(iter.next(), Some((0, 2)));
        assert_eq!(iter.next(), Some((0, 1)));
        assert_eq!(iter.next(), Some((1, 4)));
        assert_eq!(iter.next(), Some((1, 3)));
        assert_eq!(iter.next(), Some((2, 6)));
        assert_eq!(iter.next(), Some((2, 5)));
        assert_eq!(iter.next(), None);
    }
}
