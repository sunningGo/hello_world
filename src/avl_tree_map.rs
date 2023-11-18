#![allow(unused)]

use std::{
    cmp::{self, max, Ordering},
    mem,
    ops::{Bound, RangeBounds},
};

struct Node<K, V> {
    key: K,
    value: V,
    subtree_size: usize, // size of the subtree rooted at this node
    subtree_height: u8,  // height of the subtree rooted at this node
    left_child: NodePtr<K, V>,
    right_child: NodePtr<K, V>,
}

impl<K, V> Node<K, V> {
    fn new(key: K, value: V) -> Box<Self> {
        Box::new(Self {
            key,
            value,
            subtree_size: 1,
            subtree_height: 1,
            left_child: None,
            right_child: None,
        })
    }
}

impl<K: Clone, V: Clone> Clone for Node<K, V> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            value: self.value.clone(),
            subtree_size: self.subtree_size,
            subtree_height: self.subtree_height,
            left_child: self.left_child.clone(),
            right_child: self.right_child.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.key.clone_from(&source.key);
        self.value.clone_from(&source.value);
        self.subtree_size = source.subtree_size;
        self.subtree_height = source.subtree_height;
        self.left_child.clone_from(&source.left_child);
        self.right_child.clone_from(&source.right_child);
    }
}

type NodePtr<K, V> = Option<Box<Node<K, V>>>;

pub struct AvlTreeMap<K, V> {
    root: NodePtr<K, V>,
}

impl<K: Clone, V: Clone> Clone for AvlTreeMap<K, V> {
    fn clone(&self) -> Self {
        Self {
            root: self.root.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.root.clone_from(&source.root);
    }
}

impl<K, V> AvlTreeMap<K, V> {
    pub fn new() -> Self {
        AvlTreeMap { root: None }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    fn subtree_size(root_ptr: &NodePtr<K, V>) -> usize {
        match root_ptr {
            Some(b) => (**b).subtree_size,
            None => 0,
        }
    }

    fn subtree_height(root_ptr: &NodePtr<K, V>) -> u8 {
        match root_ptr {
            Some(b) => (**b).subtree_height,
            None => 0,
        }
    }

    fn balance_factor(node: &Node<K, V>) -> i8 {
        let right_subtree_height = Self::subtree_height(&node.right_child) as i16;
        let left_subtree_height = Self::subtree_height(&node.left_child) as i16;
        let balance_factor = right_subtree_height - left_subtree_height;
        debug_assert!((-2..=2).contains(&balance_factor));
        balance_factor as i8
    }

    fn subtree_size_invariant_met(root_ptr: &NodePtr<K, V>) -> bool {
        let Some(root) = root_ptr.as_deref() else {
            return true;
        };
        let left_child_ptr = &root.left_child;
        let right_child_ptr = &root.right_child;
        Self::subtree_size_invariant_met(left_child_ptr)
            && Self::subtree_size_invariant_met(right_child_ptr)
            && root.subtree_size
                == 1 + Self::subtree_size(left_child_ptr) + Self::subtree_size(right_child_ptr)
    }

    fn subtree_height_invariant_met(root_ptr: &NodePtr<K, V>) -> bool {
        let Some(root) = root_ptr.as_deref() else {
            return true;
        };
        let left_child_ptr = &root.left_child;
        let right_child_ptr = &root.right_child;
        Self::subtree_height_invariant_met(left_child_ptr)
            && Self::subtree_height_invariant_met(right_child_ptr)
            && root.subtree_height
                == 1 + cmp::max(
                    Self::subtree_height(left_child_ptr),
                    Self::subtree_height(right_child_ptr),
                )
    }

    fn bst_invariant_met_and_keys_in_range(
        root_ptr: &NodePtr<K, V>,
        range: (Bound<&K>, Bound<&K>),
    ) -> bool
    where
        K: Ord,
    {
        let Some(root) = root_ptr.as_deref() else {
            return true;
        };
        let root_key = &root.key;
        range.contains(root_key)
            && Self::bst_invariant_met_and_keys_in_range(
                &root.left_child,
                (range.start_bound(), Bound::Excluded(root_key)),
            )
            && Self::bst_invariant_met_and_keys_in_range(
                &root.right_child,
                (Bound::Excluded(root_key), range.end_bound()),
            )
    }

    fn bst_invariant_met(root_ptr: &NodePtr<K, V>) -> bool
    where
        K: Ord,
    {
        Self::bst_invariant_met_and_keys_in_range(root_ptr, (Bound::Unbounded, Bound::Unbounded))
    }

    fn avl_tree_invariant_met(root_ptr: &NodePtr<K, V>) -> bool {
        let Some(root) = root_ptr.as_deref() else {
            return true;
        };
        Self::avl_tree_invariant_met(&root.left_child)
            && Self::avl_tree_invariant_met(&root.right_child)
            && (-1..=1).contains(&Self::balance_factor(root))
    }

    fn invariants_met(&self) -> bool
    where
        K: Ord,
    {
        let root_ptr = &self.root;
        Self::subtree_size_invariant_met(root_ptr)
            && Self::subtree_height_invariant_met(root_ptr)
            && Self::bst_invariant_met(root_ptr)
            && Self::avl_tree_invariant_met(root_ptr)
    }

    fn update_subtree_size(root: &mut Node<K, V>) {
        root.subtree_size =
            1 + Self::subtree_size(&root.left_child) + Self::subtree_size(&root.right_child);
    }

    fn update_subtree_height(root: &mut Node<K, V>) {
        root.subtree_height = 1 + cmp::max(
            Self::subtree_height(&root.left_child),
            Self::subtree_height(&root.right_child),
        );
    }

    fn update_subtree_size_and_height(root: &mut Node<K, V>) {
        Self::update_subtree_size(root);
        Self::update_subtree_height(root);
    }

    pub fn len(&self) -> usize {
        Self::subtree_size(&self.root)
    }

    fn get_node(&self, key: &K) -> Option<&Node<K, V>>
    where
        K: Ord,
    {
        let mut cur_node_ptr = &self.root;
        loop {
            let cur_node = &**cur_node_ptr.as_ref()?;
            match key.cmp(&cur_node.key) {
                Ordering::Less => cur_node_ptr = &cur_node.left_child,
                Ordering::Equal => return Some(cur_node),
                Ordering::Greater => cur_node_ptr = &cur_node.right_child,
            }
        }
    }

    pub fn contains_key(&self, key: &K) -> bool
    where
        K: Ord,
    {
        self.get_node(key).is_some()
    }

    pub fn get(&self, key: &K) -> Option<&V>
    where
        K: Ord,
    {
        self.get_node(key).map({ |node| &node.value })
    }

    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        let mut cur_box = self.root.as_ref()?;
        while let Some(box_to_left_child) = &(**cur_box).left_child {
            cur_box = box_to_left_child;
        }
        let min_node = &(**cur_box);
        Some((&min_node.key, &min_node.value))
    }

    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        let mut cur_box = self.root.as_ref()?;
        while let Some(box_to_right_child) = &(**cur_box).right_child {
            cur_box = box_to_right_child;
        }
        let max_node = &**cur_box;
        Some((&max_node.key, &max_node.value))
    }

    pub fn floor(&self, key: &K) -> Option<(&K, &V)>
    where
        K: Ord,
    {
        let mut cur_node_ptr = &self.root;
        let mut candidate: Option<&Node<K, V>> = None;
        while let Some(b) = cur_node_ptr {
            let cur_node = &**b;
            match key.cmp(&cur_node.key) {
                Ordering::Less => cur_node_ptr = &cur_node.left_child,
                Ordering::Equal => return Some((&cur_node.key, &cur_node.value)),
                Ordering::Greater => {
                    candidate = Some(cur_node);
                    cur_node_ptr = &cur_node.right_child;
                }
            }
        }
        candidate.map(|node| (&node.key, &node.value))
    }

    pub fn ceiling(&self, key: &K) -> Option<(&K, &V)>
    where
        K: Ord,
    {
        let mut cur_node_ptr = &self.root;
        let mut candidate: Option<&Node<K, V>> = None;
        while let Some(b) = cur_node_ptr {
            let cur_node = &**b;
            match key.cmp(&cur_node.key) {
                Ordering::Less => {
                    candidate = Some(cur_node);
                    cur_node_ptr = &cur_node.left_child
                }
                Ordering::Equal => return Some((&cur_node.key, &cur_node.value)),
                Ordering::Greater => cur_node_ptr = &cur_node.right_child,
            }
        }
        candidate.map(|node| (&node.key, &node.value))
    }

    pub fn select(&self, mut rank: usize) -> Option<(&K, &V)> {
        let mut cur_node_ptr = &self.root;
        loop {
            let cur_node = &**(cur_node_ptr.as_ref()?);
            let left_subtree_size = Self::subtree_size(&cur_node.left_child);
            match rank.cmp(&left_subtree_size) {
                Ordering::Less => cur_node_ptr = &cur_node.left_child,
                Ordering::Equal => return Some((&cur_node.key, &cur_node.value)),
                Ordering::Greater => {
                    cur_node_ptr = &cur_node.right_child;
                    rank -= left_subtree_size + 1;
                }
            }
        }
    }

    pub fn rank(&self, key: &K) -> usize
    where
        K: Ord,
    {
        let mut cur_node_ptr = &self.root;
        let mut num_of_smaller_keys_so_far: usize = 0;
        while let Some(b) = cur_node_ptr {
            let node = &(**b);
            match key.cmp(&node.key) {
                Ordering::Less => cur_node_ptr = &node.left_child,
                Ordering::Equal => {
                    return num_of_smaller_keys_so_far + Self::subtree_size(&node.left_child)
                }
                Ordering::Greater => {
                    num_of_smaller_keys_so_far += Self::subtree_size(&node.left_child) + 1;
                    cur_node_ptr = &node.right_child;
                }
            }
        }
        num_of_smaller_keys_so_far
    }

    unsafe fn node_of(node_ptr: &mut NodePtr<K, V>) -> &mut Node<K, V> {
        debug_assert!(node_ptr.is_some());
        unsafe { &mut **node_ptr.as_mut().unwrap_unchecked() }
    }

    unsafe fn left_child_of(node: &mut Node<K, V>) -> &mut Node<K, V> {
        debug_assert!(node.left_child.is_some());
        unsafe { Self::node_of(&mut node.left_child) }
    }

    unsafe fn right_child_of(node: &mut Node<K, V>) -> &mut Node<K, V> {
        debug_assert!(node.right_child.is_some());
        unsafe { Self::node_of(&mut node.right_child) }
    }

    unsafe fn rotate_left(node_ptr: &mut NodePtr<K, V>) {
        debug_assert!(node_ptr.is_some());
        let mut node = unsafe { Self::node_of(node_ptr) };
        debug_assert!(node.right_child.is_some());
        let mut box_to_right_child = unsafe { node.right_child.take().unwrap_unchecked() };
        node.right_child = box_to_right_child.left_child.take();
        Self::update_subtree_size_and_height(node);
        box_to_right_child.left_child = (*node_ptr).take();
        Self::update_subtree_size_and_height(&mut *box_to_right_child);
        *node_ptr = Some(box_to_right_child);
    }

    unsafe fn rotate_right(node_ptr: &mut NodePtr<K, V>) {
        debug_assert!(node_ptr.is_some());
        let mut node = unsafe { Self::node_of(node_ptr) };
        debug_assert!(node.left_child.is_some());
        let mut box_to_left_child = unsafe { node.left_child.take().unwrap_unchecked() };
        node.left_child = box_to_left_child.right_child.take();
        Self::update_subtree_size_and_height(node);
        box_to_left_child.right_child = (*node_ptr).take();
        Self::update_subtree_size_and_height(&mut *box_to_left_child);
        *node_ptr = Some(box_to_left_child);
    }

    unsafe fn fix_if_left_subtree_is_too_tall(node_ptr: &mut NodePtr<K, V>) {
        debug_assert!(node_ptr.is_some());
        unsafe {
            let node = Self::node_of(node_ptr);
            if !(Self::balance_factor(node) == -2) {
                return;
            }
            debug_assert!(node.left_child.is_some());
            let left_child = Self::left_child_of(node);
            let left_child_balance_factor = Self::balance_factor(left_child);
            debug_assert!((-1..=1).contains(&left_child_balance_factor));
            if left_child_balance_factor <= 0 {
                Self::rotate_right(node_ptr);
            } else {
                debug_assert!(left_child.right_child.is_some());
                Self::rotate_left(&mut node.left_child);
                Self::rotate_right(node_ptr);
            }
        }
    }

    unsafe fn fix_if_right_subtree_is_too_tall(node_ptr: &mut NodePtr<K, V>) {
        debug_assert!(node_ptr.is_some());
        unsafe {
            let node = Self::node_of(node_ptr);
            if !(Self::balance_factor(node) == 2) {
                return;
            }
            debug_assert!(node.right_child.is_some());
            let right_child = Self::right_child_of(node);
            let right_child_balance_factor = Self::balance_factor(right_child);
            debug_assert!((-1..=1).contains(&right_child_balance_factor));
            if right_child_balance_factor >= 0 {
                Self::rotate_left(node_ptr);
            } else {
                debug_assert!(right_child.left_child.is_some());
                Self::rotate_right(&mut node.right_child);
                Self::rotate_left(node_ptr);
            }
        }
    }

    /// Insert `node` into the tree whose root is pointed to by `root_ptr`. If
    /// `node.key` already exists in the tree, then the value in the existing
    /// node containing the key is swapped with the value in `node` and the
    /// updated `node` is returned, otherwise `None` is returned.
    fn insert_node(root_ptr: &mut NodePtr<K, V>, mut node: Box<Node<K, V>>) -> NodePtr<K, V>
    where
        K: Ord,
    {
        let Some(root) = root_ptr.as_deref_mut() else {
            *root_ptr = Some(node);
            return None;
        };
        match node.key.cmp(&root.key) {
            Ordering::Equal => {
                mem::swap(&mut root.value, &mut node.value);
                Some(node)
            }
            Ordering::Less => {
                let replaced_node = Self::insert_node(&mut root.left_child, node);
                if replaced_node.is_some() {
                    return replaced_node;
                }
                root.subtree_size += 1;
                Self::update_subtree_height(root);
                unsafe { Self::fix_if_left_subtree_is_too_tall(root_ptr) };
                None
            }
            Ordering::Greater => {
                let replaced_node = Self::insert_node(&mut root.right_child, node);
                if replaced_node.is_some() {
                    return replaced_node;
                }
                root.subtree_size += 1;
                Self::update_subtree_height(root);
                unsafe { Self::fix_if_right_subtree_is_too_tall(root_ptr) };
                None
            }
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        let old_value = Self::insert_node(&mut self.root, Node::new(key, value)).map(|b| b.value);
        debug_assert!(self.invariants_met());
        old_value
    }

    /// Remove the minimum node in the non-empty tree whose root is pointed to
    /// by `root_ptr` (performing any number of rotations necessary to preserve
    /// the AVL tree invariant throughout), set its `right_child` field to
    /// `None`, and return it.
    unsafe fn remove_min_node(root_ptr: &mut NodePtr<K, V>) -> Box<Node<K, V>> {
        debug_assert!(root_ptr.is_some());
        let root = unsafe { Self::node_of(root_ptr) };
        if root.left_child.is_some() {
            let min_node = unsafe { Self::remove_min_node(&mut root.left_child) };
            root.subtree_size -= 1;
            Self::update_subtree_height(root);
            unsafe { Self::fix_if_right_subtree_is_too_tall(root_ptr) };
            min_node
        } else {
            let right_subtree = mem::take(&mut root.right_child);
            unsafe { mem::replace(root_ptr, right_subtree).unwrap_unchecked() }
        }
    }

    pub fn pop_first(&mut self) -> Option<(K, V)>
    where
        K: Ord,
    {
        if self.root.is_none() {
            None
        } else {
            let min_node = unsafe { Self::remove_min_node(&mut self.root) };
            debug_assert!(self.invariants_met());
            Some((min_node.key, min_node.value))
        }
    }

    fn remove_node(root_ptr: &mut NodePtr<K, V>, key: &K) -> NodePtr<K, V>
    where
        K: Ord,
    {
        let Some(root) = root_ptr.as_deref_mut() else {
            return None;
        };
        match key.cmp(&root.key) {
            Ordering::Equal => {
                if root.left_child.is_none() {
                    let right_subtree = mem::take(&mut root.right_child);
                    mem::replace(root_ptr, right_subtree)
                } else if root.right_child.is_none() {
                    let left_subtree = mem::take(&mut root.left_child);
                    mem::replace(root_ptr, left_subtree)
                } else {
                    let mut replacement_node =
                        unsafe { Self::remove_min_node(&mut root.right_child) };
                    replacement_node.left_child = mem::take(&mut root.left_child);
                    replacement_node.right_child = mem::take(&mut root.right_child);
                    replacement_node.subtree_size = root.subtree_size - 1;
                    Self::update_subtree_height(&mut *replacement_node);
                    let removed_node = mem::replace(root_ptr, Some(replacement_node));
                    unsafe { Self::fix_if_left_subtree_is_too_tall(root_ptr) };
                    removed_node
                }
            }
            Ordering::Less => {
                let removed_node = Self::remove_node(&mut root.left_child, key);
                if removed_node.is_none() {
                    return None;
                }
                root.subtree_size -= 1;
                Self::update_subtree_height(root);
                unsafe { Self::fix_if_right_subtree_is_too_tall(root_ptr) };
                removed_node
            }
            Ordering::Greater => {
                let removed_node = Self::remove_node(&mut root.right_child, key);
                if removed_node.is_none() {
                    return None;
                }
                root.subtree_size -= 1;
                Self::update_subtree_height(root);
                unsafe { Self::fix_if_left_subtree_is_too_tall(root_ptr) };
                removed_node
            }
        }
    }

    pub fn remove(&mut self, key: &K) -> Option<V>
    where
        K: Ord,
    {
        let removed_value = Self::remove_node(&mut self.root, key).map(|b| b.value);
        debug_assert!(self.invariants_met());
        removed_value
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        let mut iter = Iter::<K, V>(vec![]);
        let mut cur_node_ptr = &self.root;
        while let Some(b) = cur_node_ptr {
            let cur_node = &**b;
            iter.0.push(cur_node);
            cur_node_ptr = &cur_node.left_child;
        }
        iter
    }

    pub fn clear(&mut self) {
        self.root = None;
    }
}

pub struct Iter<'a, K, V>(
    Vec<&'a Node<K, V>>, // used as a stack
);

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let next_node = self.0.pop()?;
        let mut cur_node_ptr = &next_node.right_child;
        while let Some(b) = cur_node_ptr {
            let cur_node = &**b;
            self.0.push(cur_node);
            cur_node_ptr = &cur_node.left_child;
        }
        Some((&next_node.key, &next_node.value))
    }
}

impl<K, V> Default for AvlTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_something() {}
}
