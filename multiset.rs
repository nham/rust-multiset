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
