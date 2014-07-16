#![feature(default_type_params)]

extern crate collections;

pub use std::iter::{FromIterator, Peekable};
pub use collections::treemap::{TreeMap, TreeSet, Entries, RevEntries};
use multiset::{TreeMultiset};

pub mod multiset;

fn main() {
    let v1 = vec!(4i, 5, 6);
    let v2 = vec!(4i, 5, 6, 7);
    let v3 = vec!(12i, 13);
    let v4 = vec!(12i, 13, 6);

    let xs: TreeMultiset<&int> = FromIterator::from_iter(v1.iter());
    let ys: TreeMultiset<&int> = FromIterator::from_iter(v2.iter());
    let zs: TreeMultiset<&int> = FromIterator::from_iter(v3.iter());
    let ws: TreeMultiset<&int> = FromIterator::from_iter(v4.iter());

    println!("{}", xs.is_subset(&ys));
    println!("{}", xs.is_disjoint(&ys));
    println!("{}", xs.is_disjoint(&zs));
    println!("{}", ys.is_disjoint(&ws));

}
