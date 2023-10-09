#![allow(unused)]

// struct EndNode {
//     value: String,
// }

// struct NonEndNode<'v> {
//     end_node_value: &'v String,
//     next: Box<EndNode>,
// }

// fn make_chain() -> Box<NonEndNode<'static>>{
//     let end_node = Box::new(EndNode {
//         value: String::from("hello"),
//     });
//     let temp_string = String::from("temp");
//     let mut non_end_node = Box::new(NonEndNode {
//         end_node_value: &temp_string,
//         next: end_node,
//     });
//     non_end_node.end_node_value = &non_end_node.next.value;
//     non_end_node
// }

pub fn main() {
    println!("Hello from patricia.rs");


    println!("Bye");
}
