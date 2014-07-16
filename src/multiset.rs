use super::{TreeMap, TreeSet, Entries, RevEntries, Peekable};
use std::fmt;
use std::fmt::Show;
use std::default::Default;
use std::hash;

/// A implementation of the `Multiset` trait on top of the `TreeMap` container.
/// The only requirement is that the type of the elements contained ascribes to
/// the `Ord` trait.
#[deriving(Clone)]
pub struct TreeMultiset<T> {
    map: TreeMap<T,uint>,
    length: uint,
}

impl<T: PartialEq + Ord> PartialEq for TreeMultiset<T> {
    #[inline]
    fn eq(&self, other: &TreeMultiset<T>) -> bool { self.map == other.map }
}

impl<T: Ord> PartialOrd for TreeMultiset<T> {
    #[inline]
    fn partial_cmp(&self, other: &TreeMultiset<T>) -> Option<Ordering> {
        self.map.partial_cmp(&other.map)
    }
}

impl<S: hash::Writer, T: Ord + hash::Hash<S>> hash::Hash<S> for TreeMultiset<T> {
    fn hash(&self, state: &mut S) {
        for elt in self.iter() {
            elt.hash(state);
        }
    }
}

impl<T: Ord + Show> Show for TreeMultiset<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));

        for (i, x) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{}", *x));
        }

        write!(f, "}}")
    }
}

impl<T: Ord> Collection for TreeMultiset<T> {
    #[inline]
    fn len(&self) -> uint { self.length }
}

impl<T: Ord> Mutable for TreeMultiset<T> {
    #[inline]
    fn clear(&mut self) {
        self.map.clear();
        self.length = 0;
    }
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

impl<T: Ord> Default for TreeMultiset<T> {
    #[inline]
    fn default() -> TreeMultiset<T> { TreeMultiset::new() }
}

impl<T: Ord> TreeMultiset<T> {
    /// Create an empty TreeMultiset
    #[inline]
    pub fn new() -> TreeMultiset<T> { TreeMultiset {map: TreeMap::new(), length: 0} }

    /// Get the number of distinct values in the multiset
    pub fn num_distinct(&self) -> uint { self.map.len() }

    /// Get a lazy iterator over the values in the multiset.
    /// Requires that it be frozen (immutable).
    #[inline]
    pub fn iter<'a>(&'a self) -> MultisetItems<'a, T> {
        MultisetItems{iter: self.map.iter(), current: None, count: 0 }
    }

    /// Get a lazy iterator over the values in the multiset.
    /// Requires that it be frozen (immutable).
    #[inline]
    pub fn rev_iter<'a>(&'a self) -> RevMultisetItems<'a, T> {
        RevMultisetItems{iter: self.map.rev_iter(), current: None, count: 0}
    }

    /// Visit the values (in-order) representing the difference
    pub fn difference<'a>(&'a self, other: &'a TreeMultiset<T>) 
        -> DifferenceItems<'a, T, MultisetItems<'a, T>> {
        DifferenceItems{a: self.iter().peekable(), b: other.iter().peekable()}
    }

    /// Visit the values (in-order) representing the symmetric difference
    pub fn symmetric_difference<'a>(&'a self, other: &'a TreeMultiset<T>)
        -> SymDifferenceItems<'a, T, MultisetItems<'a, T>> {
        SymDifferenceItems{a: self.iter().peekable(), b: other.iter().peekable()}
    }

    /// Visit the values (in-order) representing the multiset sum
    pub fn sum<'a>(&'a self, other: &'a TreeMultiset<T>)
        -> SumItems<'a, T, MultisetItems<'a, T>> {
        SumItems{a: self.iter().peekable(), b: other.iter().peekable()}
    }

    /// Visit the values (in-order) representing the intersection
    pub fn intersection<'a>(&'a self, other: &'a TreeMultiset<T>)
        -> IntersectionItems<'a, T, MultisetItems<'a, T>> {
        IntersectionItems{a: self.iter().peekable(), b: other.iter().peekable()}
    }

    /// Visit the values (in-order) representing the union
    pub fn union<'a>(&'a self, other: &'a TreeMultiset<T>) 
        -> UnionItems<'a, T, MultisetItems<'a, T>> {
        UnionItems{a: self.iter().peekable(), b: other.iter().peekable()}
    }

    /// Return the number of occurrences of the value in the multiset.
    #[inline]
    pub fn count(&self, value: &T) -> uint {
        match self.map.find(value) {
            None => 0u,
            Some(count) => *count
        }
    }

    /// Return true if the multiset has no elements in common with `other`.
    pub fn is_disjoint(&self, other: &TreeMultiset<T>) -> bool {
        let mut x = self.iter();
        let mut y = other.iter();
        let mut a = x.next();
        let mut b = y.next();
        while a.is_some() && b.is_some() {
            let a1 = a.unwrap();
            let b1 = b.unwrap();

            match a1.cmp(b1) {
                Less => a = x.next(),
                Greater => b = y.next(),
                Equal => return false,
            }
        }
        true
    }

    /// Return true if, for any given element, the number times it occurs in the
    /// multiset is not greater than the number of times it occurs in `other`.
    pub fn is_subset(&self, other: &TreeMultiset<T>) -> bool {
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

    /// Return true if the value occurs at least once in the multiset.
    pub fn contains(&self, value: &T) -> bool {
        self.count(value) > 0u
    }

    /// Return true if the multiset is a superset of another.
    pub fn is_superset(&self, other: &TreeMultiset<T>) -> bool {
        other.is_subset(self)
    }

    /// Add `n` occurrences of `value` to the multiset. Return true if the value
    /// was not already present in the multiset.
    pub fn insert_many(&mut self, value: T, n: uint) -> bool {
        let curr = self.count(&value);
        self.length += n;
        self.map.insert(value, curr + n)
    }

    /// Remove `n` occurrences of `value` from the multiset. If there are less
    /// than `n` occurrences, remove all occurrences. Return the number of
    /// occurrences removed.
    pub fn remove_many(&mut self, value: &T, n: uint) -> uint {
        let curr = self.count(value);

        if n >= curr {
            self.map.remove(value);
            self.length -= curr;
            curr
        } else {
            match self.map.find_mut(value) {
                None => 0u,
                Some(mult) => {
                    self.length -= n;
                    *mult = curr - n;
                    n
                }
            }
        }
    }

    /// Add one occurrence of `value` to the multiset. Return true if the value
    /// was not already present in the multiset.
    pub fn insert(&mut self, value: T) -> bool {
        self.insert_many(value, 1)
    }

    /// Remove one occurrence of `value` from the multiset. Return true if the
    /// value was present in the multiset.
    pub fn remove(&mut self, value: &T) -> bool {
        self.remove_many(value, 1) > 0u
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

/// Lazy backward iterator over a multiset
pub struct RevMultisetItems<'a, T> {
    iter: RevEntries<'a, T, uint>,
    current: Option<&'a T>,
    count: uint,
}

/// Lazy iterator producing elements in the set difference (in-order)
pub struct DifferenceItems<'a, T, I> {
    a: Peekable<&'a T, I>,
    b: Peekable<&'a T, I>,
}

/// Lazy iterator producing elements in the set symmetric difference (in-order)
pub struct SymDifferenceItems<'a, T, I> {
    a: Peekable<&'a T, I>,
    b: Peekable<&'a T, I>,
}

/// Lazy iterator producing elements in the multiset sum (in-order)
pub struct SumItems<'a, T, I> {
    a: Peekable<&'a T, I>,
    b: Peekable<&'a T, I>,
}

/// Lazy iterator producing elements in the set intersection (in-order)
pub struct IntersectionItems<'a, T, I> {
    a: Peekable<&'a T, I>,
    b: Peekable<&'a T, I>,
}

/// Lazy iterator producing elements in the set union (in-order)
pub struct UnionItems<'a, T, I> {
    a: Peekable<&'a T, I>,
    b: Peekable<&'a T, I>,
}

impl<'a, T> Iterator<&'a T> for MultisetItems<'a, T> {
    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.count == 0 {
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
        self.count -= 1;
        self.current
    }
}

impl<'a, T> Iterator<&'a T> for RevMultisetItems<'a, T> {
    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.count == 0 {
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
        self.count -= 1;
        self.current
    }
}

/// Compare `x` and `y`, but return `short` if x is None and `long` if y is None
fn cmp_opt<T: Ord>(x: Option<&T>, y: Option<&T>,
                        short: Ordering, long: Ordering) -> Ordering {
    match (x, y) {
        (None    , _       ) => short,
        (_       , None    ) => long,
        (Some(x1), Some(y1)) => x1.cmp(y1),
    }
}

impl<'a, T: Ord, I: Iterator<&'a T>> Iterator<&'a T> for DifferenceItems<'a, T, I> {
    fn next(&mut self) -> Option<&'a T> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), Less, Less) {
                Less    => return self.a.next(),
                Equal   => { self.a.next(); self.b.next(); }
                Greater => { self.b.next(); }
            }
        }
    }
}

impl<'a, T: Ord, I: Iterator<&'a T>> Iterator<&'a T> for SymDifferenceItems<'a, T, I> {
    fn next(&mut self) -> Option<&'a T> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), Greater, Less) {
                Less    => return self.a.next(),
                Equal   => { self.a.next(); self.b.next(); }
                Greater => return self.b.next(),
            }
        }
    }
}

impl<'a, T: Ord, I: Iterator<&'a T>> Iterator<&'a T> for SumItems<'a, T, I> {
    fn next(&mut self) -> Option<&'a T> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), Greater, Less) {
                Less    => return self.a.next(),
                Equal   => return self.a.next(),
                Greater => return self.b.next(),
            }
        }
    }
}

impl<'a, T: Ord, I: Iterator<&'a T>> Iterator<&'a T> for IntersectionItems<'a, T, I> {
    fn next(&mut self) -> Option<&'a T> {
        loop {
            let o_cmp = match (self.a.peek(), self.b.peek()) {
                (None    , _       ) => None,
                (_       , None    ) => None,
                (Some(a1), Some(b1)) => Some(a1.cmp(b1)),
            };
            match o_cmp {
                None          => return None,
                Some(Less)    => { self.a.next(); }
                Some(Equal)   => { self.b.next(); return self.a.next() }
                Some(Greater) => { self.b.next(); }
            }
        }
    }
}

impl<'a, T: Ord, I: Iterator<&'a T>> Iterator<&'a T> for UnionItems<'a, T, I> {
    fn next(&mut self) -> Option<&'a T> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), Greater, Less) {
                Less    => return self.a.next(),
                Equal   => { self.b.next(); return self.a.next() }
                Greater => return self.b.next(),
            }
        }
    }
}

mod test_mset {
    use super::{TreeMultiset};
    use std::hash;

    #[test]
    fn test_len() {
        let mut s = TreeMultiset::new();
        assert!(s.len() == 0);
        assert!(s.insert(1i));
        assert!(s.len() == 1);
        assert!(s.insert_many(3, 5));
        assert!(s.len() == 6);
        assert!(s.insert_many(7, 2));
        assert!(s.len() == 8);

        assert!(s.remove(&7));
        assert!(s.len() == 7);
        assert!(s.remove(&7));
        assert!(s.len() == 6);
        assert!(!s.remove(&7));
        assert!(s.len() == 6);
        assert!(s.remove_many(&3, 3) == 3);
        assert!(s.len() == 3);
        assert!(s.remove_many(&3, 8) == 2);
        assert!(s.len() == 1);
    }

    #[test]
    fn test_clear() {
        let mut s = TreeMultiset::new();
        s.clear();
        assert!(s.insert(5i));
        assert!(s.insert(12));
        assert!(s.insert(19));
        s.clear();
        assert!(!s.contains(&5));
        assert!(!s.contains(&12));
        assert!(!s.contains(&19));
        assert!(s.is_empty());
    }

    #[test]
    fn test_count() {
        let mut m = TreeMultiset::new();
        assert!(m.insert(1i));
        assert!(m.count(&1) == 1);
        assert!(!m.insert(1i));
        assert!(m.count(&1) == 2);

        assert!(m.count(&2) == 0);
        assert!(m.insert_many(2i, 4));
        assert!(m.count(&2) == 4);
        assert!(m.remove_many(&2, 3) == 3);
        assert!(m.count(&2) == 1);
        assert!(m.remove(&2));
        assert!(m.count(&2) == 0);
        assert!(!m.remove(&2));
        assert!(m.count(&2) == 0);
    }

    #[test]
    fn test_disjoint() {
        let mut xs = TreeMultiset::new();
        let mut ys = TreeMultiset::new();
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(xs.insert(5i));
        assert!(ys.insert(11i));
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(xs.insert(7));
        assert!(xs.insert(19));
        assert!(xs.insert(4));
        assert!(ys.insert(2));
        assert!(ys.insert(-11));
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(ys.insert(7));
        assert!(!ys.is_disjoint(&xs));
        assert!(!xs.is_disjoint(&ys));
        assert!(!xs.insert(7));
        assert!(!ys.is_disjoint(&xs));
        assert!(!xs.is_disjoint(&ys));
    }

    #[test]
    fn test_subset_and_superset() {
        let mut a = TreeMultiset::new();
        assert!(a.insert(0i));
        assert!(a.insert(5));
        assert!(a.insert(11));
        assert!(a.insert(7));

        let mut b = TreeMultiset::new();
        assert!(b.insert(0i));
        assert!(b.insert(7));
        assert!(b.insert(19));
        assert!(b.insert(250));
        assert!(b.insert(11));
        assert!(b.insert(200));

        assert!(!a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(!b.is_superset(&a));

        assert!(!a.insert(5));
        assert!(b.insert(5));

        assert!(!a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(!b.is_superset(&a));

        assert!(!b.insert(5));

        assert!(a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(b.is_superset(&a));

        assert!(!b.insert(7));
        assert!(!b.insert(7));

        assert!(a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(b.is_superset(&a));
    }

    #[test]
    fn test_iterator() {
        let mut m = TreeMultiset::new();

        assert!(m.insert(3i));
        assert!(m.insert(2));
        assert!(m.insert(0));
        assert!(m.insert(-2));
        assert!(m.insert(4));
        assert!(!m.insert(2));
        assert!(m.insert(1));

        let v = vec!(-2i, 0, 1, 2, 2, 3, 4);
        for (x, y) in m.iter().zip(v.iter()) {
            assert_eq!(*x, *y);
        }
    }

    #[test]
    fn test_rev_iter() {
        let mut m = TreeMultiset::new();

        assert!(m.insert(3i));
        assert!(m.insert(2));
        assert!(m.insert(0));
        assert!(m.insert(-2));
        assert!(m.insert(4));
        assert!(!m.insert(2));
        assert!(m.insert(1));

        let v = vec!(4i, 3, 2, 2, 1, 0, -2);
        for (x, y) in m.rev_iter().zip(v.iter()) {
            assert_eq!(*x, *y);
        }
    }

    #[test]
    fn test_clone_eq() {
      let mut m = TreeMultiset::new();

      m.insert(1i);
      m.insert(2);

      assert!(m.clone() == m);
    }

    #[test]
    fn test_hash() {
      let mut x = TreeMultiset::new();
      let mut y = TreeMultiset::new();

      x.insert(1i);
      x.insert(2);
      x.insert(3);

      y.insert(3i);
      y.insert(2);
      y.insert(1);

      assert!(hash::hash(&x) == hash::hash(&y));
    }

    fn check(a: &[int],
             b: &[int],
             expected: &[int],
             f: |&TreeMultiset<int>, &TreeMultiset<int>, f: |&int| -> bool| -> bool) {
        let mut set_a = TreeMultiset::new();
        let mut set_b = TreeMultiset::new();

        for x in a.iter() { set_a.insert(*x); }
        for y in b.iter() { set_b.insert(*y); }

        let mut i = 0;
        f(&set_a, &set_b, |x| {
            assert_eq!(*x, expected[i]);
            i += 1;
            true
        });
        assert_eq!(i, expected.len());
    }

    #[test]
    fn test_intersection() {
        fn check_intersection(a: &[int], b: &[int], expected: &[int]) {
            check(a, b, expected, |x, y, f| x.intersection(y).all(f))
        }

        check_intersection([], [], []);
        check_intersection([1, 2, 3, 2], [], []);
        check_intersection([], [1, 2, 3, 2], []);
        check_intersection([2], [1, 2, 3], [2]);
        check_intersection([2, 2], [1, 2, 3, 2], [2, 2]);
        check_intersection([1, 2, 3, 2], [2, 2], [2, 2]);
        check_intersection([11, 5, 5, 1, 3, 77, 103, 5, -5, 1, 1, 77],
                           [2, 11, 77, -9, -42, 5, 3, 77, 2, 5],
                           [3, 5, 5, 11, 77, 77]);
    }

    #[test]
    fn test_difference() {
        fn check_difference(a: &[int], b: &[int], expected: &[int]) {
            check(a, b, expected, |x, y, f| x.difference(y).all(f))
        }

        check_difference([], [], []);
        check_difference([1, 12], [], [1, 12]);
        check_difference([1, 12, 1], [], [1, 1, 12]);
        check_difference([], [1, 2, 2, 3, 9], []);
        check_difference([1, 3, 3, 3, 5, 9, 11],
                         [3, 9, 3],
                         [1, 3, 5, 11]);
        check_difference([-5, 11, 22, 33, 40, 42],
                         [-12, -5, 14, 23, 34, 38, 39, 50],
                         [11, 22, 33, 40, 42]);
    }

    #[test]
    fn test_symmetric_difference() {
        fn check_symmetric_difference(a: &[int], b: &[int],
                                      expected: &[int]) {
            check(a, b, expected, |x, y, f| x.symmetric_difference(y).all(f))
        }

        check_symmetric_difference([], [], []);
        check_symmetric_difference([1, 1, 2, 3], [2], [1, 1, 3]);
        check_symmetric_difference([2, 2], [1, 2, 2, 3], [1, 3]);
        check_symmetric_difference([1, 3, 5, 9, 11],
                                   [-2, 3, 9, 14, 22],
                                   [-2, 1, 5, 11, 14, 22]);
    }

    #[test]
    fn test_sum() {
        fn check_sum(a: &[int], b: &[int],
                                      expected: &[int]) {
            check(a, b, expected, |x, y, f| x.sum(y).all(f))
        }

        check_sum([], [], []);
        check_sum([1, 2, 2, 3], [2], [1, 2, 2, 2, 3]);
        check_sum([2, 2], [1, 2, 2, 3], [1, 2, 2, 2, 2, 3]);
        check_sum([1, 3, 5, 9, 11, 16, 19, 24],
                    [-2, 1, 5, 9, 13, 19],
                    [-2, 1, 1, 3, 5, 5, 9, 9, 11, 13, 16, 19, 19, 24]);
    }

    #[test]
    fn test_union() {
        fn check_union(a: &[int], b: &[int],
                                      expected: &[int]) {
            check(a, b, expected, |x, y, f| x.union(y).all(f))
        }

        check_union([], [], []);
        check_union([1, 2, 2, 3], [2], [1, 2, 2, 3]);
        check_union([2, 2, 2], [1, 2, 2, 3], [1, 2, 2, 2, 3]);
        check_union([1, 3, 5, 9, 11, 16, 19, 24],
                    [-2, 1, 5, 9, 13, 19],
                    [-2, 1, 3, 5, 9, 11, 13, 16, 19, 24]);
    }

    #[test]
    fn test_from_iter() {
        let xs = [1i, 2, 3, 3, 3, 4, 5, 4, 6, 7, 8, 9];

        let set: TreeMultiset<int> = xs.iter().map(|&x| x).collect();

        for x in xs.iter() {
            if *x == 3 {
                assert!(set.count(x) == 3);
            } else if *x == 4 {
                assert!(set.count(x) == 2);
            } else {
                assert!(set.count(x) == 1);
            }
        }
    }

    #[test]
    fn test_show() {
        let mut set: TreeMultiset<int> = TreeMultiset::new();
        let empty: TreeMultiset<int> = TreeMultiset::new();

        set.insert(1);
        set.insert_many(2, 3);

        let set_str = format!("{}", set);

        assert!(set_str == "{1, 2, 2, 2}".to_string());
        assert_eq!(format!("{}", empty), "{}".to_string());
    }
}
