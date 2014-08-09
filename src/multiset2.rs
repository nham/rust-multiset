use super::{TreeMap, TreeSet, Entries, RevEntries, Peekable};
use std::default::Default;
use std::collections::DList;

struct P<T> {
    ptr: *const T,
}

impl P<T> {
    fn new(p: &T) -> P<T> {
        P { ptr: p as *const T }
    }
}

impl<T: PartialEq> PartialEq for P<T> {
    fn eq(&self, other: &P<T>) -> bool {
        unsafe { &*self.ptr == &*other.ptr }
    }
}

impl<T: Eq> Eq for P<T> { }

impl<T: PartialOrd> PartialOrd for P<T> {
    fn partial_cmp(&self, other: &P<T>) -> Option<Ordering> {
        unsafe { (&*self.ptr).partial_cmp(&*other.ptr) }
    }
}

impl<T: Ord> Ord for P<T> {
    fn cmp(&self, other: &P<T>) -> Ordering {
        unsafe { (&*self.ptr).cmp(&*other.ptr) }
    }
}

/// A implementation of the `Multiset` trait on top of the `TreeMap` container.
/// The only requirement is that the type of the elements contained ascribes to
/// the `Ord` trait.
#[deriving(Clone)]
pub struct TreeMultiset<T> {
    map: TreeMap<P<T>,DList<T>>,
    size: uint,
}

impl<T: Ord> Collection for TreeMultiset<T> {
    #[inline]
    fn len(&self) -> uint { self.size }
}

impl<T: Ord> Mutable for TreeMultiset<T> {
    #[inline]
    fn clear(&mut self) {
        self.map.clear();
        self.size = 0;
    }
}

impl<T: Ord> Default for TreeMultiset<T> {
    #[inline]
    fn default() -> TreeMultiset<T> { TreeMultiset::new() }
}

impl<T: Ord> Extendable<T> for TreeMultiset<T> {
    #[inline]
    fn extend<Iter: Iterator<T>>(&mut self, mut iter: Iter) {
        for elem in iter {
            self.insert(elem);
        }
    }
}

impl<T: Ord> FromIterator<T> for TreeMultiset<T> {
    fn from_iter<Iter: Iterator<T>>(iter: Iter) -> TreeMultiset<T> {
        let mut mset = TreeMultiset::new();
        mset.extend(iter);
        mset
    }
}

impl<T: Ord> TreeMultiset<T> {
    /// Create an empty TreeMultiset
    #[inline]
    pub fn new() -> TreeMultiset<T> { TreeMultiset {map: TreeMap::new(), size: 0} }

    /// Get the number of distinct values in the multiset
    pub fn num_distinct(&self) -> uint { self.map.len() }

    /// Get a lazy iterator over the values in the multiset.
    /// Requires that it be frozen (immutable).
    #[inline]
    pub fn iter<'a>(&'a self) -> MultisetItems<'a, T> {
        MultisetItems{iter: self.map.iter(), current: None, count: 0 }
    }
}
