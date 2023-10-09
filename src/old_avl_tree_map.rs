#![allow(unused)]

use std::{
    cmp::{self, Ordering},
    mem,
};

// Balance factor
#[derive(Clone, Copy)]
enum Bf {
    LeftHeavy,
    EquallyHeavy,
    RightHeavy,
}

struct Node<K: Ord, V> {
    key: K,
    value: V,
    subtree_size: usize, // number of nodes in the subtree rooted at this node
    bf: Bf,
    left_child: NodePtr<K, V>,
    right_child: NodePtr<K, V>,
}

impl<K: Ord, V> Node<K, V> {
    fn new(key: K, value: V) -> Box<Node<K, V>> {
        Box::new(Node {
            key,
            value,
            subtree_size: 1,
            bf: Bf::EquallyHeavy,
            left_child: None,
            right_child: None,
        })
    }
}

type NodePtr<K, V> = Option<Box<Node<K, V>>>;

struct AvlTreeMap<K: Ord, V> {
    root: NodePtr<K, V>,
}

#[derive(PartialEq, Eq)]
enum HeightInc {
    Yes,
    No,
}

#[derive(PartialEq, Eq)]
enum HeightDec {
    Yes,
    No,
}

impl<K: Ord, V> AvlTreeMap<K, V> {
    pub fn new() -> AvlTreeMap<K, V> {
        AvlTreeMap { root: None }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    fn subtree_size(root: &NodePtr<K, V>) -> usize {
        match root {
            Some(b) => (**b).subtree_size,
            None => 0,
        }
    }

    fn update_subtree_size(node: &mut Node<K, V>) {
        node.subtree_size =
            1 + Self::subtree_size(&node.left_child) + Self::subtree_size(&node.right_child);
    }

    pub fn len(&self) -> usize {
        Self::subtree_size(&self.root)
    }

    fn get_node(&self, key: &K) -> Option<&Node<K, V>> {
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

    pub fn contains_key(&self, key: &K) -> bool {
        self.get_node(key).is_some()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
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

    pub fn floor(&self, key: &K) -> Option<(&K, &V)> {
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

    pub fn ceiling(&self, key: &K) -> Option<(&K, &V)> {
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

    pub fn rank(&self, key: &K) -> usize {
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
        unsafe { &mut **node_ptr.as_mut().unwrap_unchecked() }
    }

    unsafe fn left_child_of(node: &mut Node<K, V>) -> &mut Node<K, V> {
        unsafe { &mut **node.left_child.as_mut().unwrap_unchecked() }
    }

    unsafe fn right_child_of(node: &mut Node<K, V>) -> &mut Node<K, V> {
        unsafe { &mut **node.right_child.as_mut().unwrap_unchecked() }
    }

    unsafe fn rotate_left(node_ptr: &mut NodePtr<K, V>) {
        let mut node = Self::node_of(node_ptr);
        let mut box_to_right_child = node.right_child.take().unwrap_unchecked();
        node.right_child = box_to_right_child.left_child.take();
        Self::update_subtree_size(node);
        box_to_right_child.left_child = (*node_ptr).take();
        Self::update_subtree_size(&mut *box_to_right_child);
        *node_ptr = Some(box_to_right_child);
    }

    unsafe fn rotate_right(node_ptr: &mut NodePtr<K, V>) {
        let mut node = Self::node_of(node_ptr);
        let mut box_to_left_child = node.left_child.take().unwrap_unchecked();
        node.left_child = box_to_left_child.right_child.take();
        Self::update_subtree_size(node);
        box_to_left_child.right_child = (*node_ptr).take();
        Self::update_subtree_size(&mut *box_to_left_child);
        *node_ptr = Some(box_to_left_child);
    }

    // Assuming that there is a violation of the AVL tree invariant at the root pointed to by
    // root_node_ptr in that the height of the left subtree is greater than that of the right
    // subtree by two (but that the invariant is satisfied at every other node), fix the violation
    // (by a right rotation or a left-right rotation at the root) and then return an indication of
    // whether the fix resulted in a decrease of the height of the overall tree.
    unsafe fn fix_left_taller_by_two(root_node_ptr: &mut NodePtr<K, V>) -> HeightDec {
        unsafe {
            let root = Self::node_of(root_node_ptr);
            let left_child = Self::left_child_of(root);
            match left_child.bf {
                Bf::LeftHeavy => {
                    Self::rotate_right(root_node_ptr);
                    let new_root = Self::node_of(root_node_ptr);
                    new_root.bf = Bf::EquallyHeavy;
                    Self::right_child_of(new_root).bf = Bf::EquallyHeavy;
                    HeightDec::Yes
                }
                Bf::EquallyHeavy => {
                    Self::rotate_right(root_node_ptr);
                    let new_root = Self::node_of(root_node_ptr);
                    new_root.bf = Bf::RightHeavy;
                    Self::right_child_of(new_root).bf = Bf::LeftHeavy;
                    HeightDec::No
                }
                Bf::RightHeavy => {
                    let grand_child_bf = Self::right_child_of(left_child).bf;
                    Self::rotate_left(&mut root.left_child);
                    Self::rotate_right(root_node_ptr);
                    let new_root = Self::node_of(root_node_ptr);
                    new_root.bf = Bf::EquallyHeavy;
                    match grand_child_bf {
                        Bf::LeftHeavy => {
                            Self::left_child_of(new_root).bf = Bf::EquallyHeavy;
                            Self::right_child_of(new_root).bf = Bf::RightHeavy;
                        }
                        Bf::EquallyHeavy => {
                            Self::left_child_of(new_root).bf = Bf::EquallyHeavy;
                            Self::right_child_of(new_root).bf = Bf::EquallyHeavy;
                        }
                        Bf::RightHeavy => {
                            Self::left_child_of(new_root).bf = Bf::LeftHeavy;
                            Self::right_child_of(new_root).bf = Bf::EquallyHeavy;
                        }
                    };
                    HeightDec::Yes
                }
            }
        }
    }

    // A comment similar to that on fix_left_taller_than_right_by_two applies here.
    unsafe fn fix_right_taller_by_two(root_node_ptr: &mut NodePtr<K, V>) -> HeightDec {
        unsafe {
            let root = Self::node_of(root_node_ptr);
            let right_child = Self::right_child_of(root);
            match right_child.bf {
                Bf::RightHeavy => {
                    Self::rotate_left(root_node_ptr);
                    let new_root = Self::node_of(root_node_ptr);
                    new_root.bf = Bf::EquallyHeavy;
                    Self::left_child_of(new_root).bf = Bf::EquallyHeavy;
                    HeightDec::Yes
                }
                Bf::EquallyHeavy => {
                    Self::rotate_left(root_node_ptr);
                    let new_root = Self::node_of(root_node_ptr);
                    new_root.bf = Bf::LeftHeavy;
                    Self::left_child_of(new_root).bf = Bf::RightHeavy;
                    HeightDec::No
                }
                Bf::LeftHeavy => {
                    let grand_child_bf = Self::left_child_of(right_child).bf;
                    Self::rotate_right(&mut root.right_child);
                    Self::rotate_left(root_node_ptr);
                    let new_root = Self::node_of(root_node_ptr);
                    new_root.bf = Bf::EquallyHeavy;
                    match grand_child_bf {
                        Bf::LeftHeavy => {
                            Self::left_child_of(new_root).bf = Bf::EquallyHeavy;
                            Self::right_child_of(new_root).bf = Bf::RightHeavy;
                        }
                        Bf::EquallyHeavy => {
                            Self::left_child_of(new_root).bf = Bf::EquallyHeavy;
                            Self::right_child_of(new_root).bf = Bf::EquallyHeavy;
                        }
                        Bf::RightHeavy => {
                            Self::left_child_of(new_root).bf = Bf::LeftHeavy;
                            Self::right_child_of(new_root).bf = Bf::EquallyHeavy;
                        }
                    };
                    HeightDec::Yes
                }
            }
        }
    }

    fn insert_node(
        root_node_ptr: &mut NodePtr<K, V>,
        mut node: Box<Node<K, V>>,
    ) -> (HeightInc, NodePtr<K, V>) {
        let Some(b) = root_node_ptr else {
            *root_node_ptr = Some(node);
            return (HeightInc::Yes, None);
        };
        let root = &mut **b;
        match node.key.cmp(&root.key) {
            Ordering::Less => {
                let (left_subtree_height_inc, replaced_node) =
                    Self::insert_node(&mut root.left_child, node);
                if replaced_node.is_none() {
                    root.subtree_size += 1;
                }
                if left_subtree_height_inc == HeightInc::No {
                    return (HeightInc::No, replaced_node);
                }
                match root.bf {
                    Bf::LeftHeavy => {
                        let height_dec = unsafe { Self::fix_left_taller_by_two(root_node_ptr) };
                        debug_assert!(height_dec == HeightDec::Yes);
                        (HeightInc::No, replaced_node)
                    }
                    Bf::EquallyHeavy => {
                        root.bf = Bf::LeftHeavy;
                        (HeightInc::Yes, replaced_node)
                    }
                    Bf::RightHeavy => {
                        root.bf = Bf::EquallyHeavy;
                        (HeightInc::No, replaced_node)
                    }
                }
            }
            Ordering::Equal => {
                node.left_child = mem::take(&mut root.left_child);
                node.right_child = mem::take(&mut root.right_child);
                node.subtree_size = root.subtree_size;
                node.bf = root.bf;
                (HeightInc::No, mem::replace(root_node_ptr, Some(node)))
            }
            Ordering::Greater => {
                let (right_subtree_height_inc, replaced_node) =
                    Self::insert_node(&mut root.right_child, node);
                if replaced_node.is_none() {
                    root.subtree_size += 1;
                }
                if right_subtree_height_inc == HeightInc::No {
                    return (HeightInc::No, replaced_node);
                }
                match root.bf {
                    Bf::LeftHeavy => {
                        root.bf = Bf::EquallyHeavy;
                        (HeightInc::No, replaced_node)
                    }
                    Bf::EquallyHeavy => {
                        root.bf = Bf::RightHeavy;
                        (HeightInc::Yes, replaced_node)
                    }
                    Bf::RightHeavy => {
                        let height_dec = unsafe { Self::fix_right_taller_by_two(root_node_ptr) };
                        debug_assert!(height_dec == HeightDec::Yes);
                        (HeightInc::No, replaced_node)
                    }
                }
            }
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        Self::insert_node(&mut self.root, Node::new(key, value))
            .1
            .map(|b| b.value)
    }

    // Remove the minimum node in the non-empty tree whose root is pointed to by root_node_ptr
    // (performing any number of rotations necessary to preserve the AVL tree invariant throughout),
    // and return a tuple whose 0-th component indicates whether the height of the tree decreased as
    // a result and whose 1-st component is the minimum node removed.
    //
    // The tree must be non-empty when this function is called (or else UB will result). The
    // returned minimum node will have its left_child and right_child fields set to None. But the
    // subtree_size and the bf fields will have some unspecified values. (In particular, the
    // subtree_size field may not be 1 and the bf field may not be Bf::EquallyHeavy.)
    unsafe fn remove_min_node(root_node_ptr: &mut NodePtr<K, V>) -> (HeightDec, Box<Node<K, V>>) {
        debug_assert!(root_node_ptr.is_some());
        let root = unsafe { &mut **root_node_ptr.as_mut().unwrap_unchecked() };
        if root.left_child.is_some() {
            let (left_subtree_height_dec, min_node) = Self::remove_min_node(&mut root.left_child);
            root.subtree_size -= 1;
            if left_subtree_height_dec == HeightDec::No {
                return (HeightDec::No, min_node);
            }
            match root.bf {
                Bf::LeftHeavy => {
                    root.bf = Bf::EquallyHeavy;
                    return (HeightDec::Yes, min_node);
                }
                Bf::EquallyHeavy => {
                    root.bf = Bf::RightHeavy;
                    return (HeightDec::No, min_node);
                }
                Bf::RightHeavy => {
                    let height_dec = unsafe { Self::fix_right_taller_by_two(root_node_ptr) };
                    return (height_dec, min_node);
                }
            }
        } else {
            let right_subtree = mem::take(&mut root.right_child);
            return unsafe {
                (
                    HeightDec::Yes,
                    mem::replace(root_node_ptr, right_subtree).unwrap_unchecked(),
                )
            };
        }
    }

    pub fn pop_first(&mut self) -> Option<(K, V)> {
        if self.root.is_none() {
            None
        } else {
            let min_node = unsafe { Self::remove_min_node(&mut self.root).1 };
            Some((min_node.key, min_node.value))
        }
    }

    fn remove_node(root_node_ptr: &mut NodePtr<K, V>, key: &K) -> (HeightDec, NodePtr<K, V>) {
        let Some(b) = root_node_ptr else {
            return (HeightDec::No, None);
        };
        let root = &mut **b;
        match key.cmp(&root.key) {
            Ordering::Equal => {
                if root.left_child.is_none() {
                    let right_subtree = mem::take(&mut root.right_child);
                    (HeightDec::Yes, mem::replace(root_node_ptr, right_subtree))
                } else if root.right_child.is_none() {
                    let left_subtree = mem::take(&mut root.left_child);
                    (HeightDec::Yes, mem::replace(root_node_ptr, left_subtree))
                } else {
                    let (right_subtree_height_dec, mut replacement_node) =
                        unsafe { Self::remove_min_node(&mut root.right_child) };
                    replacement_node.left_child = mem::take(&mut root.left_child);
                    replacement_node.right_child = mem::take(&mut root.right_child);
                    replacement_node.subtree_size = root.subtree_size - 1;
                    replacement_node.bf = root.bf;
                    let removed_node = mem::replace(root_node_ptr, Some(replacement_node));
                    let root = unsafe { Self::node_of(root_node_ptr) };
                    match root.bf {
                        Bf::LeftHeavy => {
                            if right_subtree_height_dec == HeightDec::Yes {
                                let height_dec =
                                    unsafe { Self::fix_left_taller_by_two(root_node_ptr) };
                                (height_dec, removed_node)
                            } else {
                                (HeightDec::No, removed_node)
                            }
                        }
                        Bf::EquallyHeavy => {
                            if right_subtree_height_dec == HeightDec::Yes {
                                root.bf = Bf::LeftHeavy
                            };
                            (HeightDec::No, removed_node)
                        }
                        Bf::RightHeavy => {
                            if right_subtree_height_dec == HeightDec::Yes {
                                root.bf = Bf::EquallyHeavy
                            };
                            (right_subtree_height_dec, removed_node)
                        }
                    }
                }
            }
            Ordering::Less => {
                let (left_subtree_height_dec, removed_node) =
                    Self::remove_node(&mut root.left_child, key);
                if removed_node.is_none() {
                    return (HeightDec::No, None);
                }
                root.subtree_size -= 1;
                match root.bf {
                    Bf::LeftHeavy => {
                        if left_subtree_height_dec == HeightDec::Yes {
                            root.bf = Bf::EquallyHeavy;
                        }
                        (left_subtree_height_dec, removed_node)
                    }
                    Bf::EquallyHeavy => {
                        if left_subtree_height_dec == HeightDec::Yes {
                            root.bf = Bf::RightHeavy;
                        }
                        (HeightDec::No, removed_node)
                    }
                    Bf::RightHeavy => {
                        if left_subtree_height_dec == HeightDec::Yes {
                            unsafe { (Self::fix_right_taller_by_two(root_node_ptr), removed_node) }
                        } else {
                            (HeightDec::No, removed_node)
                        }
                    }
                }
            }
            Ordering::Greater => {
                let (right_subtree_height_dec, removed_node) =
                    Self::remove_node(&mut root.right_child, key);
                if removed_node.is_none() {
                    return (HeightDec::No, None);
                }
                root.subtree_size -= 1;
                match root.bf {
                    Bf::LeftHeavy => {
                        if right_subtree_height_dec == HeightDec::Yes {
                            unsafe { (Self::fix_left_taller_by_two(root_node_ptr), removed_node) }
                        } else {
                            (HeightDec::No, removed_node)
                        }
                    }
                    Bf::EquallyHeavy => {
                        if right_subtree_height_dec == HeightDec::Yes {
                            root.bf = Bf::LeftHeavy;
                        }
                        (HeightDec::No, removed_node)
                    }
                    Bf::RightHeavy => {
                        if right_subtree_height_dec == HeightDec::Yes {
                            root.bf = Bf::EquallyHeavy;
                        }
                        (right_subtree_height_dec, removed_node)
                    }
                }
            }
        }
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        Self::remove_node(&mut self.root, key).1.map(|b| b.value)
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

struct Iter<'a, K: Ord, V>(
    Vec<&'a Node<K, V>>, // used as a stack
);

impl<'a, K: Ord, V> Iterator for Iter<'a, K, V> {
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
