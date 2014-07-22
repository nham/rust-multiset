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

    let mut xs: TreeMultiset<int> = v1.move_iter().collect();
    let mut ys: TreeMultiset<int> = v2.move_iter().collect();
    let mut zs: TreeMultiset<int> = v3.move_iter().collect();
    let mut ws: TreeMultiset<int> = v4.move_iter().collect();

    println!("{}", xs.is_subset(&ys));
    println!("{}", xs.is_disjoint(&ys));
    println!("{}", xs.is_disjoint(&zs));
    println!("{}", ys.is_disjoint(&ws));

    xs.insert_many(6, 2);
    xs.insert_many(9, 3);
    xs.insert(15);
    xs.insert_many(5, 1);

    for x in xs.lower_bound(&6) {
        println!("{}", x);
    }

    for x in xs.upper_bound(&6) {
        println!("{}", x);
    }

}
