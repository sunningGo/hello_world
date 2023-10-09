#![allow(unused)]


fn balance_factor(x: u8, y: u8) -> i8 {
    let diff = x as i16 - y as i16;
    debug_assert!(-2 <= diff && diff <= 2);
    diff as i8
}

fn balance_factor2(x: u8, y: u8) -> i8 {
    let diff = x - y;
    0
}

pub fn main() {
    println!("Hello from simple_tests");

    println!("{}", balance_factor(1, 3));

    println!("Bye");
}
