//@ [!lean] skip

// Function-item call lifetimes are not borrows stored in the callable value.
#![allow(dead_code)]
fn apply<F: FnMut(&u8) -> u8>(mut f: F, x: &u8) -> u8 {
    f(x)
}
fn checked(x: &u8) -> u8 {
    *x + 1
}
pub fn through_function_item(x: &u8) -> u8 {
    apply(checked, x)
}
