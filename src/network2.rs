#![allow(dead_code)]

use std::{
    cell::{RefCell, UnsafeCell},
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
    hash::Hash,
    mem::transmute,
};

pub struct Network<'network, NodeId> {
    nodes: RefCell<HashMap<NodeId, Box<UnsafeCell<Node<'network, NodeId>>>>>,
}

impl<'network, NodeId: Copy + Eq + Hash> Network<'network, NodeId> {
    pub fn new() -> Network<'network, NodeId> {
        Network {
            nodes: RefCell::new(HashMap::new()),
        }
    }

    pub fn get_or_insert_node<'node_borrow>(
        &'node_borrow self,
        id: NodeId,
    ) -> NodePtr<'network, 'node_borrow, NodeId>
    where
        'network: 'node_borrow,
    {
        let mut nodes = self.nodes.borrow_mut();
        let node_creating_closure = || {
            Box::new(UnsafeCell::new(Node {
                network: unsafe { transmute::<_, &'network Network<'network, NodeId>>(self) },
                id: id,
                neighbor_id_s: HashSet::new(),
                visit_count: 0,
            }))
        };
        let ref_to_unsafe_cell = &**nodes.entry(id).or_insert_with(node_creating_closure);
        NodePtr(unsafe {
            transmute::<_, &'node_borrow UnsafeCell<Node<'network, NodeId>>>(ref_to_unsafe_cell)
        })
    }

    fn get_node<'node_borrow>(
        &'node_borrow self,
        id: NodeId,
    ) -> Option<NodePtr<'network, 'node_borrow, NodeId>> {
        let nodes = self.nodes.borrow();
        nodes.get(&id).map(|r| {
            NodePtr(unsafe {
                transmute::<_, &'node_borrow UnsafeCell<Node<'network, NodeId>>>(&**r)
            })
        })
    }

    fn delete_node(&mut self, id: NodeId) {
        let mut nodes = self.nodes.borrow_mut();
        nodes.remove(&id);
    }
}

#[derive(Clone, Copy)]
pub struct NodePtr<'network, 'node_borrow, NodeId>(
    &'node_borrow UnsafeCell<Node<'network, NodeId>>,
);

pub struct Node<'network, NodeId> {
    network: &'network Network<'network, NodeId>,
    id: NodeId,
    neighbor_id_s: HashSet<NodeId>,
    visit_count: usize,
}

impl<'network, NodeId: Copy + Eq + Hash + Debug + 'network> Node<'network, NodeId> {
    pub fn id(&self) -> NodeId {
        self.id
    }

    pub fn add_neighbor(node_ptr: NodePtr<NodeId>, neighbor_id: NodeId) {
        unsafe {
            (*node_ptr.0.get()).neighbor_id_s.insert(neighbor_id);
        }
    }

    pub fn rm_neighbor(node_ptr: NodePtr<NodeId>, neighbor_id: NodeId) {
        unsafe {
            (*node_ptr.0.get()).neighbor_id_s.remove(&neighbor_id);
        }
    }

    pub fn traverse(node_ptr: NodePtr<NodeId>, path: &mut VecDeque<NodeId>) -> Result<(), String> {
        unsafe {
            let node_ptr = node_ptr.0.get();
            let node_id = (*node_ptr).id();
            println!("Node {:?} is visited", node_id);
            (*node_ptr).visit_count += 1;
            if path.is_empty() {
                return Ok(());
            }
            let next_node_id = path[0];
            if !(*node_ptr).neighbor_id_s.contains(&next_node_id) {
                return Err(String::from(format!(
                    "{:?} is not a neighbor of {:?}",
                    next_node_id, node_id
                )));
            }
            match (*node_ptr).network.get_node(next_node_id) {
                Some(next_node_ptr) => {
                    path.pop_front();
                    return Self::traverse(next_node_ptr, path);
                }
                None => {
                    return Err(String::from(format!(
                        "Network has no node with id {next_node_id:?}"
                    )));
                }
            }
        }
    }
}

//#[test]
pub fn main() {
    let mut network = Network::<usize>::new();
    let node_0 = network.get_or_insert_node(0);
    let node_1 = network.get_or_insert_node(1);
    let node_2 = network.get_or_insert_node(2);
    let node_3 = network.get_or_insert_node(3);

    Node::add_neighbor(node_0, 1);
    Node::add_neighbor(node_1, 2);
    Node::add_neighbor(node_2, 3);
    Node::add_neighbor(node_3, 0);

    if let Err(msg) = Node::traverse(node_0, &mut VecDeque::from([1, 2, 3, 0, 1])) {
        eprintln!("{msg}");
    }

    network.delete_node(3);
}
