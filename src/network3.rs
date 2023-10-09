#![allow(dead_code)]

use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    mem::transmute,
};

pub struct Network<'network, NodeId> {
    nodes: RefCell<HashMap<NodeId, Box<Node<'network, NodeId>>>>,
}

impl<'network, NodeId: Copy + Eq + Hash + Debug> Network<'network, NodeId> {
    pub fn new() -> Network<'network, NodeId> {
        Network {
            nodes: RefCell::new(HashMap::new()),
        }
    }

    pub fn get_or_insert_node<'a>(&'a self, id: NodeId) -> &'a Node<'network, NodeId> {
        let mut nodes = self.nodes.borrow_mut();
        let node_creating_closure = || {
            Box::new(Node {
                network: unsafe{ transmute::<_, &'network Network<'network, NodeId>>(self)},
                id: id,
                neighbor_id_s: RefCell::new(HashSet::new()),
                visit_count: Cell::new(0),
            })
        };
        let node = nodes.entry(id).or_insert_with(node_creating_closure);
        unsafe {transmute::<_, &'a Node<'network, NodeId>>(&**node)}
    }

    pub fn get_node<'a>(&'a self, id: NodeId) -> Option<&'a Node<'network, NodeId>> {
        let nodes = self.nodes.borrow();
        let node = nodes.get(&id).map(|r| &**r);
        unsafe {transmute::<_, Option<&'a Node<'network, NodeId>>>(node)}
    }

    pub fn print(&self) {
        for (node_id, node) in &*self.nodes.borrow() {
            print!("{:?}: ", node_id);
            println!("{:?}", node.get_neighbors())
        }
    }

    pub fn rm_node(&mut self, id: NodeId) {
        self.nodes.borrow_mut().remove(&id);
        for (_, node) in &*self.nodes.borrow_mut() {
            node.rm_neighbor(id);
        }
    }
}

pub struct Node<'network, Id> {
    network: &'network Network<'network, Id>,
    id: Id,
    neighbor_id_s: RefCell<HashSet<Id>>,
    visit_count: Cell<usize>,
}

impl<'nodes, Id: Copy + Eq + Hash + Debug> Node<'nodes, Id> {
    pub fn id(&self) -> Id {
        self.id
    }

    pub fn add_neighbor(&self, neighbor_id: Id) {
        self.neighbor_id_s.borrow_mut().insert(neighbor_id);
    }

    pub fn rm_neighbor(&self, neighbor_id: Id) {
        self.neighbor_id_s.borrow_mut().remove(&neighbor_id);
    }

    pub fn get_neighbors<'a>(&'a self) -> &'a HashSet<Id> {
        unsafe {transmute::<_, &'a HashSet<Id>>(&*self.neighbor_id_s.borrow())}
    }

    pub fn traverse<I: Iterator<Item=Id>>(&self, path: &mut I) -> Result<(), String> {
        println!("Node {:?} is visited", self.id());
        self.visit_count.set(self.visit_count.get() + 1);
        let next_node_id_option = path.next();
        if next_node_id_option.is_none() {
            return Ok(());
        }
        let next_node_id = next_node_id_option.unwrap();
        if !self.neighbor_id_s.borrow().contains(&next_node_id) {
            return Err(String::from(format!(
                "{:?} is not a neighbor of {:?}",
                next_node_id,
                self.id()
            )));
        }
        match self.network.get_node(next_node_id) {
            Some(next_node) => {
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
    let mut network = Network::<usize>::new();
    let node_0 = network.get_or_insert_node(0);
    let node_1 = network.get_or_insert_node(1);
    let node_2 = network.get_or_insert_node(2);
    let node_3 = network.get_or_insert_node(3);
    node_0.add_neighbor(1);
    node_1.add_neighbor(2);
    node_2.add_neighbor(3);
    node_3.add_neighbor(0);
    network.print();
    if let Err(msg) = node_0.traverse(&mut [1, 2, 3, 0, 1].into_iter()) {
        eprintln!("{msg}");
    }
    network.rm_node(2);
    network.print();
}
