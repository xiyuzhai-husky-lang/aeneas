//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

// Keep operations symbolic so Rust constant folding cannot hide a bad lowering.
pub fn eq32(x: f32, y: f32) -> bool {
    x == y
}
pub fn ne32(x: f32, y: f32) -> bool {
    x != y
}
pub fn lt32(x: f32, y: f32) -> bool {
    x < y
}
pub fn le32(x: f32, y: f32) -> bool {
    x <= y
}
pub fn gt32(x: f32, y: f32) -> bool {
    x > y
}
pub fn ge32(x: f32, y: f32) -> bool {
    x >= y
}
pub fn neg32(x: f32) -> f32 {
    -x
}
pub fn eq64(x: f64, y: f64) -> bool {
    x == y
}
pub fn ne64(x: f64, y: f64) -> bool {
    x != y
}
pub fn lt64(x: f64, y: f64) -> bool {
    x < y
}
pub fn le64(x: f64, y: f64) -> bool {
    x <= y
}
pub fn gt64(x: f64, y: f64) -> bool {
    x > y
}
pub fn ge64(x: f64, y: f64) -> bool {
    x >= y
}
pub fn neg64(x: f64) -> f64 {
    -x
}

pub fn constants32() -> (f32, f32, f32, f32, f32, f32) {
    (0.0, -0.0, 0.1, 1.17549435e-38, 3.40282347e38, 1.0e-45)
}
pub fn constants64() -> (f64, f64, f64, f64, f64, f64) {
    (
        0.0,
        -0.0,
        0.1,
        2.2250738585072014e-308,
        1.7976931348623157e308,
        5.0e-324,
    )
}

#[verify::test]
pub fn comparisons() {
    assert!(eq32(0.0, -0.0));
    assert!(eq64(0.0, -0.0));
    assert!(!lt32(0.0, -0.0));
    assert!(lt32(-2.0, -1.0));
    assert!(le32(-1.0, 0.0));
    assert!(gt32(2.0, 1.0));
    assert!(ge32(1.0, 1.0));
    assert!(ne32(1.0, 2.0));
    assert!(lt64(-2.0, -1.0));
    assert!(le64(-1.0, 0.0));
    assert!(gt64(2.0, 1.0));
    assert!(ge64(1.0, 1.0));
    assert!(ne64(1.0, 2.0));
    assert!(eq32(neg32(1.0), -1.0));
    assert!(eq64(neg64(1.0), -1.0));
}

// Overflowing literals exercise Charon's infinity spelling directly.
#[allow(overflowing_literals)]
pub fn infinities32() -> (f32, f32) {
    (1.0e100, -1.0e100)
}
#[allow(overflowing_literals)]
pub fn infinities64() -> (f64, f64) {
    (1.0e400, -1.0e400)
}
