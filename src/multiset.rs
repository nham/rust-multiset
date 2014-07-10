use super::{TreeMap, TreeSet, Entries};

pub trait Multiset<T>: Collection {
    /// Return the number occurrences of the value in the multiset
    fn count(&self, value: &T) -> uint;

    /// Return true if the multiset has no elements in common with `other`.
    fn is_disjoint(&self, other: &Self) -> bool;

    /// Return true if every element x contained in the multiset has a multiplicity 
    /// not greater than x's multiplicity in `other`
    fn is_subset(&self, other: &Self) -> bool;

    /// Return true if the value occurs at least once in the multiset
    fn contains(&self, value: &T) -> bool {
        self.count(value) > 0u
    }

    /// Return true if the multiset is a superset of another
    fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
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
    fn remove(&mut self, value: &T, n: uint) -> uint;

    /// Add one occurrence of `value` to the multiset. Return true if the value
    /// was not already present in the multiset.
    fn insert_one(&mut self, value: T) -> bool {
        self.insert(value, 1)
    }
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


impl<T: Ord> Extendable<T> for TreeMultiset<T> {
    #[inline]
    fn extend<Iter: Iterator<T>>(&mut self, mut iter: Iter) {
        for elem in iter {
            self.insert(elem, 1);
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

impl<T: Ord> Multiset<T> for TreeMultiset<T> {
    #[inline]
    fn count(&self, value: &T) -> uint {
        match self.map.find(value) {
            None => 0u,
            Some(count) => *count
        }
    }

    fn is_disjoint(&self, other: &TreeMultiset<T>) -> bool {
        let mut x = self.iter();
        let mut y = other.iter();
        let mut a = x.next();
        let mut b = y.next();
        while a.is_some() {
            if b.is_none() {
                return true;
            }

            let a1 = a.unwrap();
            let b1 = b.unwrap();

            match b1.cmp(a1) {
                Less => (),
                Greater => a = x.next(),
                Equal => return false,
            }

            b = y.next();
        }
        true
    }

    fn is_subset(&self, other: &TreeMultiset<T>) -> bool {
        let mut x = self.iter();
        let mut y = other.iter();
        let mut a = x.next();
        let mut b = y.next();
        while a.is_some() {
            if b.is_none() {
                return false;
            }

            let a1 = a.unwrap();
            let b1 = b.unwrap();

            match b1.cmp(a1) {
                Less => (),
                Greater => return false,
                Equal => a = x.next(),
            }

            b = y.next();
        }
        true
    }

}


impl<T: Ord> MutableMultiset<T> for TreeMultiset<T> {
    fn insert(&mut self, value: T, n: uint) -> bool {
        let curr = self.count(&value);
        self.map.insert(value, curr + n)
    }

    fn remove(&mut self, value: &T, n: uint) -> uint {
        let curr = self.count(value);

        if n >= curr {
            self.map.remove(value);
            curr
        } else {
            match self.map.find_mut(value) {
                None => 0u,
                Some(mult) => {
                    *mult = curr - n;
                    n
                }
            }
        }
    }

}


impl<T: Ord> TreeMultiset<T> {
    /// Create an empty TreeMultiset
    #[inline]
    pub fn new() -> TreeMultiset<T> { TreeMultiset {map: TreeMap::new()} }

    /// Get a lazy iterator over the values in the multiset.
    /// Requires that it be frozen (immutable).
    #[inline]
    pub fn iter<'a>(&'a self) -> MultisetItems<'a, T> {
        MultisetItems{iter: self.map.iter(), current: None, count: 0 }
    }
}

impl<T: Ord + Clone> TreeMultiset<T> {
    pub fn to_set(&self) -> TreeSet<T> {
        let mut set = TreeSet::new();
        for (k, _) in self.map.clone().move_iter() {
            set.insert(k);
        }
        set
    }
}


/// Lazy forward iterator over a multiset
pub struct MultisetItems<'a, T> {
    iter: Entries<'a, T, uint>,
    current: Option<&'a T>,
    count: uint,
}

impl<'a, T> Iterator<&'a T> for MultisetItems<'a, T> {
    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.count == 0u {
            // Either we've exhausted the multiset or we just need to grab
            // the next entry from self.iter
            match self.iter.next() {
                None => return None,
                Some((val, count)) => {
                    self.current = Some(val);
                    self.count = *count;
                }
            }
        }

        // Assume here that we will never have an entry with a count of zero.
        // This means we have to take care that when we remove the last occurrence 
        // from a multiset, we must delete the key also.
        self.current
    }
}
