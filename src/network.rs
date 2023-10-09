#![allow(dead_code)]

use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
    hash::Hash,
    mem::transmute,
};

pub struct Network<'a, NodeId> {
    nodes: RefCell<HashMap<NodeId, Box<Node<'a, NodeId>>>>,
}

impl<'a, NodeId: Copy + Eq + Hash> Network<'a, NodeId> {
    pub fn new() -> Network<'a, NodeId> {
        Network {
            nodes: RefCell::new(HashMap::new()),
        }
    }

    pub fn get_or_insert_node(&'a self, id: NodeId) -> &'a Node<'a, NodeId> {
        let mut nodes = self.nodes.borrow_mut();
        let node = nodes.entry(id).or_insert_with(|| {
            Box::new(Node {
                network: self,
                id: id,
                neighbor_id_s: RefCell::new(HashSet::new()),
                visit_count: Cell::new(0),
            })
        });
        unsafe { transmute::<&Node<NodeId>, &'a Node<'a, NodeId>>(&**node) }
    }

    fn get_node(&self, id: NodeId) -> Option<&'a Node<'a, NodeId>> {
        self.nodes
            .borrow()
            .get(&id)
            .map(|node| unsafe { transmute::<&Node<NodeId>, &'a Node<'a, NodeId>>(&**node) })
    }
}

pub struct Node<'a, Id> {
    network: &'a Network<'a, Id>,
    id: Id,
    neighbor_id_s: RefCell<HashSet<Id>>,
    visit_count: Cell<usize>,
}

impl<'a, Id: Copy + Eq + Hash + Debug> Node<'a, Id> {
    pub fn id(&self) -> Id {
        self.id
    }

    pub fn add_neighbor(&self, neighbor_id: Id) {
        self.neighbor_id_s.borrow_mut().insert(neighbor_id);
    }

    pub fn traverse(&'a self, path: &mut VecDeque<Id>) -> Result<(), String> {
        println!("Node {:?} is visited", self.id());
        self.visit_count.set(self.visit_count.get() + 1);
        if path.is_empty() {
            return Ok(());
        }
        let next_node_id = path[0];
        if !self.neighbor_id_s.borrow().contains(&next_node_id) {
            return Err(String::from(format!(
                "{:?} is not a neighbor of {:?}",
                next_node_id,
                self.id()
            )));
        }
        match self.network.get_node(next_node_id) {
            Some(next_node) => {
                path.pop_front();
                return next_node.traverse(path);
            }
            None => {
                return Err(String::from(format!(
                    "Network has no node with id {next_node_id:?}"
                )));
            }
        }
    }
}

//#[test]
pub fn main() {
    let network = Network::<usize>::new();
    let node_0 = network.get_or_insert_node(0);
    let node_1 = network.get_or_insert_node(1);
    let node_2 = network.get_or_insert_node(2);
    let node_3 = network.get_or_insert_node(3);
    node_0.add_neighbor(1);
    node_1.add_neighbor(2);
    node_2.add_neighbor(3);
    node_3.add_neighbor(0);
    if let Err(msg) = node_0.traverse(&mut VecDeque::from([1, 2, 3, 0, 1])) {
        eprintln!("{msg}");
    }
}
