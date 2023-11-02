fn main() {
    let r1 = Rectangle {
        height: 1,
        width: 12,
    };
    let r2 = Rectangle {
        height: 1,
        width: 12,
    };
    println!(
        "rec area: {:?} can hold: {:?} ",
        r1.area(),
        r1.can_hold(&r2)
    );
    let ip0 = IpAddr::V4(255, 0, 0, 0);
    println!("ip: {:?}", ip0);
    println!("value: {:?}", value_cents(&Coin::Quarter(UsState::Alabama)));
}

#[derive(Debug)]
struct Rectangle {
    height: u32,
    width: u32,
}

impl Rectangle {
    fn area(&self) -> u32 {
        self.width * self.height
    }
    fn can_hold(&self, rec: &Rectangle) -> bool {
        self.width >= rec.width && self.height >= rec.height
    }
}

#[derive(Debug)]
enum IpAddr {
    V4(u32, u32, u32, u32),
    V6(String),
}

#[derive(Debug)]
enum UsState {
    Alaska,
    Alabama,
}

enum Coin {
    Penny,
    Nickel,
    Dime,
    Quarter(UsState),
}

fn value_cents(c: &Coin) -> u8 {
    match c {
        Coin::Penny => 1,
        Coin::Nickel => 5,
        Coin::Dime => 10,
        Coin::Quarter(state) => {
            println!("quarter from {:?}", state);
            25
        }
    }
}
