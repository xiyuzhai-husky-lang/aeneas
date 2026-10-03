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

pub fn add32(x: f32, y: f32) -> f32 {
    x + y
}

pub fn sub32(x: f32, y: f32) -> f32 {
    x - y
}

pub fn mul32(x: f32, y: f32) -> f32 {
    x * y
}

pub fn div32(x: f32, y: f32) -> f32 {
    x / y
}

pub fn rem32(x: f32, y: f32) -> f32 {
    x % y
}

pub fn add64(x: f64, y: f64) -> f64 {
    x + y
}

pub fn sub64(x: f64, y: f64) -> f64 {
    x - y
}

pub fn mul64(x: f64, y: f64) -> f64 {
    x * y
}

pub fn div64(x: f64, y: f64) -> f64 {
    x / y
}

pub fn rem64(x: f64, y: f64) -> f64 {
    x % y
}

pub fn f32_to_i32(x: f32) -> i32 {
    x as i32
}

pub fn i32_to_f32(x: i32) -> f32 {
    x as f32
}

pub fn f32_to_u32(x: f32) -> u32 {
    x as u32
}

pub fn u32_to_f32(x: u32) -> f32 {
    x as f32
}

pub fn f32_to_i64(x: f32) -> i64 {
    x as i64
}

pub fn i64_to_f32(x: i64) -> f32 {
    x as f32
}

pub fn f32_to_u64(x: f32) -> u64 {
    x as u64
}

pub fn u64_to_f32(x: u64) -> f32 {
    x as f32
}

pub fn f32_to_i128(x: f32) -> i128 {
    x as i128
}

pub fn i128_to_f32(x: i128) -> f32 {
    x as f32
}

pub fn f32_to_u128(x: f32) -> u128 {
    x as u128
}

pub fn u128_to_f32(x: u128) -> f32 {
    x as f32
}

pub fn f32_to_isize(x: f32) -> isize {
    x as isize
}

pub fn isize_to_f32(x: isize) -> f32 {
    x as f32
}

pub fn f32_to_usize(x: f32) -> usize {
    x as usize
}

pub fn usize_to_f32(x: usize) -> f32 {
    x as f32
}

pub fn f64_to_i32(x: f64) -> i32 {
    x as i32
}

pub fn i32_to_f64(x: i32) -> f64 {
    x as f64
}

pub fn f64_to_u32(x: f64) -> u32 {
    x as u32
}

pub fn u32_to_f64(x: u32) -> f64 {
    x as f64
}

pub fn f64_to_i64(x: f64) -> i64 {
    x as i64
}

pub fn i64_to_f64(x: i64) -> f64 {
    x as f64
}

pub fn f64_to_u64(x: f64) -> u64 {
    x as u64
}

pub fn u64_to_f64(x: u64) -> f64 {
    x as f64
}

pub fn f64_to_i128(x: f64) -> i128 {
    x as i128
}

pub fn i128_to_f64(x: i128) -> f64 {
    x as f64
}

pub fn f64_to_u128(x: f64) -> u128 {
    x as u128
}

pub fn u128_to_f64(x: u128) -> f64 {
    x as f64
}

pub fn f64_to_isize(x: f64) -> isize {
    x as isize
}

pub fn isize_to_f64(x: isize) -> f64 {
    x as f64
}

pub fn f64_to_usize(x: f64) -> usize {
    x as usize
}

pub fn usize_to_f64(x: usize) -> f64 {
    x as f64
}

pub fn f32_to_f64(x: f32) -> f64 {
    x as f64
}
pub fn f64_to_f32(x: f64) -> f32 {
    x as f32
}
