extern crate collections;

use collections::treemap::{TreeMap, TreeSet};

pub trait Multiset<T>: Collection {
    /// Return the number occurrences of the value in the multiset
    fn count(&self, value: &T) -> uint;

    /// Return true if the set has no elements in common with `other`.
    fn is_disjoint(&self, other: &Self) -> bool;

    /// Return true if every element x contained in the multiset has a multiplicity 
    /// not greater than x's multiplicity in `other`
    fn is_subset(&self, other: &Self) -> bool;

    /// Return true if the value occurs at least once in the multiset
    fn contains(&self, value: &T) -> bool {
        self.count(value) > 0u
    }

    // FIXME: Ideally we would have a method to return the underlying set
    // of a multiset. However, currently there's no way to have a trait method 
    // return a trait. We need something like associated type synonyms (see #5033)
}

pub trait MutableMultiset<T>: Multiset<T> + Mutable {
    /// Add `n` occurrences of `value` to the multiset. Return true if the value
    /// was not already present in the multiset.
    fn insert(&mut self, value: T, n: uint) -> bool;

    /// Remove `n` occurrences of `value` from the multiset. If there are less than
    /// `n` occurrences, remove all occurrences. Return the number of occurrences
    /// removed.
    fn remove(&mut self, value: T, n: uint) -> uint;
}


pub struct TreeMultiset<T> {
    map: TreeMap<T,uint>,
}

impl<T: Ord> Collection for TreeMultiset<T> {
    #[inline]
    fn len(&self) -> uint { self.map.len() }
}

impl<T: Ord> Mutable for TreeMultiset<T> {
    #[inline]
    fn clear(&mut self) { self.map.clear() }
}



impl<T: Ord + Clone> TreeMultiset<T> {
    fn to_set(&self) -> TreeSet<T> {
        let mut set = TreeSet::new();
        for (k, _) in self.map.clone().move_iter() {
            set.insert(k);
        }
        set
    }
}

fn main() {}
