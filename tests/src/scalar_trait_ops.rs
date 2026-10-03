//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub fn add(x: u32, y: u32) -> u32 {
    std::ops::Add::add(x, y)
}
pub fn sub(x: u32, y: u32) -> u32 {
    std::ops::Sub::sub(x, y)
}
pub fn rem(x: u32, y: u32) -> u32 {
    std::ops::Rem::rem(x, y)
}
pub fn not(x: u32) -> u32 {
    std::ops::Not::not(x)
}
pub fn and(x: u32, y: u32) -> u32 {
    std::ops::BitAnd::bitand(x, y)
}
pub fn or(x: u32, y: u32) -> u32 {
    std::ops::BitOr::bitor(x, y)
}
pub fn xor(x: u32, y: u32) -> u32 {
    std::ops::BitXor::bitxor(x, y)
}
pub fn shl(x: u32, n: usize) -> u32 {
    std::ops::Shl::shl(x, n)
}
pub fn shr(x: u32, n: usize) -> u32 {
    std::ops::Shr::shr(x, n)
}

#[verify::test]
pub fn check_arithmetic() {
    assert!(add(0xffff_fffe, 1) == 0xffff_ffff);
    assert!(sub(0xffff_ffff, 1) == 0xffff_fffe);
    assert!(sub(0, 0) == 0);
    assert!(rem(0xffff_ffff, 32) == 31);
    assert!(rem(0xffff_ffff, 1) == 0);
}

#[verify::test]
pub fn check_bits() {
    assert!(not(0) == 0xffff_ffff);
    assert!(and(0xffff_ffff, 0x8000_0001) == 0x8000_0001);
    assert!(or(0x8000_0000, 1) == 0x8000_0001);
    assert!(xor(0x8000_0001, 0x8000_0000) == 1);
    assert!(shl(1, 31) == 0x8000_0000);
    assert!(shl(0x8000_0000, 1) == 0);
    assert!(shr(0x8000_0000, 31) == 1);
    assert!(shr(0xffff_ffff, 0) == 0xffff_ffff);
}
