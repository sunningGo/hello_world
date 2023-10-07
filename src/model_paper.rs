#![allow(unused)]

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::fmt::Display;
use std::hint::spin_loop;
use std::ops::Bound::Included;
use std::{clone, mem};

fn make_separator(user_str: &str) -> &str {
    const DEFAULT: &str = "==========";
    if user_str == "" {
        DEFAULT
    } else {
        user_str
    }
}

fn get_or_default(arg: &Option<String>) -> String {
    match arg {
        Some(s) => s.clone(),
        None => String::new(),
    }
}

fn find_nth<T: Ord + Clone>(elems: &mut [T], n: usize) -> T {
    elems.sort();
    let t = &elems[n];
    return t.clone();
}

fn remove_zeros_0(v: &mut Vec<i32>) {
    let indexes_of_zeros = v
        .iter()
        .enumerate()
        .filter_map(|(i, &n)| if n == 0 { Some(i) } else { None })
        .collect::<Vec<_>>();
    for i in indexes_of_zeros {
        v.remove(i);
    }
}

pub fn find<T, P: Fn(&T) -> bool>(s: &[T], start_index: usize, predicate: P) -> Option<usize> {
    let s_len = s.len();
    if !(start_index <= s_len) {
        panic!(
            "start_index ({}) should be less than or equal to s.len() ({})",
            start_index, s_len
        );
    }
    let mut i = start_index;
    loop {
        if i == s_len {
            return None;
        }
        if predicate(&s[i]) {
            return Some(i);
        }
        i += 1;
    }
}

fn remove_zeros_1(v: &mut Vec<i32>) {
    let is_zero = |n: &i32| *n == 0;
    let Some(mut index_to_fill) = find(v, 0, is_zero) else {
        return;
    };
    let is_not_zero = |n: &i32| *n != 0;
    let Some(mut index_to_move) = find(v, index_to_fill + 1, is_not_zero) else {
        return;
    };
    loop {
        v[index_to_fill] = v[index_to_move];
        index_to_fill += 1;
        index_to_move = if let Some(next_index_to_move) = find(v, index_to_move + 1, is_not_zero) {
            next_index_to_move
        } else {
            return;
        }
    }
}

struct TestResult {
    /// Student's scores on a test
    scores: Vec<usize>,
    /// A possible value to curve all sores
    curve: Option<usize>,
}

impl TestResult {
    pub fn get_curve(&self) -> &Option<usize> {
        &self.curve
    }

    pub fn apply_curve(&mut self) {
        if let Some(curve) = &self.curve {
            for score in self.scores.iter_mut() {
                *score += *curve;
            }
        }
    }
}

fn reverse_0<T>(v: &mut Vec<T>) {
    let n = v.len();
    for i in 0..n / 2 {
        let (_, s0) = v.split_at_mut(i);
        let (s0, s1) = s0.split_at_mut(n - 1 - 2 * i);
        mem::swap(&mut s0[0], &mut s1[0]);
    }
}

fn get_pair_from_slice_mut<T>(s: &mut [T], i: usize, j: usize) -> Option<(&mut T, &mut T)> {
    let s_len = s.len();
    if !(i < s_len) {
        panic!();
    }
    if !(j < s_len) {
        panic!();
    }
    if i == j {
        return None;
    }
    Some((unsafe { &mut *(&mut s[i] as *mut T) }, unsafe {
        &mut *(&mut s[j] as *mut T)
    }))
}

unsafe fn get_pair_from_slice_mut_unchecked<T>(
    s: &mut [T],
    i: usize,
    j: usize,
) -> (&mut T, &mut T) {
    unsafe { (&mut *(&mut s[i] as *mut T), &mut *(&mut s[j] as *mut T)) }
}

fn reverse_1<T>(v: &mut Vec<T>) {
    let n = v.len();
    for i in 0..n / 2 {
        let (r1, r2) = unsafe { get_pair_from_slice_mut_unchecked(v, i, n - 1 - i) };
        mem::swap(r1, r2);
    }
}

fn concat_all<'s>(
    iter: impl Iterator<Item = String> + 's,
    s: &'s str,
) -> impl Iterator<Item = String> + 's {
    iter.map(move |s2| s2 + s)
}

fn add_displayable_0<T: Display + 'static>(v: &mut Vec<Box<dyn Display>>, t: T) {
    v.push(Box::new(t));
}

fn add_displayable_1<'a, T: Display + 'a>(v: &mut Vec<Box<dyn Display + 'a>>, t: T) {
    v.push(Box::new(t));
}

pub fn main() {
    println!("Hello from model_paper.rs");
    let mut v = vec![0, 1, 2, 3];
    reverse_1(&mut v);
    println!("{:?}", v);
    println!("Bye");
}
