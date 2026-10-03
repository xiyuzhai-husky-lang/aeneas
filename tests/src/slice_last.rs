//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub fn last<T>(xs: &[T]) -> Option<&T> {
    xs.last()
}

pub fn last_or(xs: &[u32], fallback: u32) -> u32 {
    match xs.last() {
        Some(x) => *x,
        None => fallback,
    }
}

#[verify::test]
pub fn check_last() {
    assert!(last_or(&[], 7) == 7);
    assert!(last_or(&[11], 7) == 11);
    assert!(last_or(&[1, 4, 9], 7) == 9);
}
