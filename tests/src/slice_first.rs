//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub fn first<T>(xs: &[T]) -> Option<&T> {
    xs.first()
}

pub fn first_or(xs: &[u32], fallback: u32) -> u32 {
    match xs.first() {
        Some(x) => *x,
        None => fallback,
    }
}

#[verify::test]
pub fn check_first() {
    assert!(first_or(&[], 7) == 7);
    assert!(first_or(&[11], 7) == 11);
    assert!(first_or(&[1, 4, 9], 7) == 1);
}
