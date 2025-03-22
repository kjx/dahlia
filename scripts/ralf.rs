 
enum XpAddr {
    X4{a: u8, b: u8, c: u8, d: u8},
//    X6(String),
 }  //from Rust book
 
 

 


 fn main() { 
     let mut s = XpAddr::X4{a: 100, b: 0, c: 0, d: 1}; 
     s.b == 42;
     if let XpAddr::X4{..} = s { s.b = 42; };
// //     s = XpAddr::X6(String::from("whoops"));
//      let b : u8 = s.1;
    }