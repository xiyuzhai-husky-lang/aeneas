//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub fn truncate<T>(v: &mut Vec<T>, len: usize) {
    v.truncate(len);
}
pub fn as_slice<T>(v: &Vec<T>) -> &[T] {
    v.as_slice()
}
pub fn remove<T>(v: &mut Vec<T>, index: usize) -> T {
    v.remove(index)
}
pub fn pop<T>(v: &mut Vec<T>) -> Option<T> {
    v.pop()
}
pub fn clear<T>(v: &mut Vec<T>) {
    v.clear();
}
pub fn is_empty<T>(v: &Vec<T>) -> bool {
    v.is_empty()
}
pub fn retain<T, F: FnMut(&T) -> bool>(v: &mut Vec<T>, pred: F) {
    v.retain(pred);
}
pub fn dedup<T: PartialEq>(v: &mut Vec<T>) {
    v.dedup();
}

#[verify::test]
pub fn check_endpoints() {
    let mut v = Vec::new();
    assert!(is_empty(&v));
    assert!(pop(&mut v).is_none());
    v.push(10u32);
    v.push(20u32);
    v.push(30u32);
    assert!(remove(&mut v, 1) == 20);
    assert!(as_slice(&v).len() == 2);
    assert!(as_slice(&v)[0] == 10);
    assert!(as_slice(&v)[1] == 30);
    assert!(pop(&mut v).unwrap() == 30);
    assert!(remove(&mut v, 0) == 10);
    assert!(is_empty(&v));
}

#[verify::test]
pub fn check_truncate_and_clear() {
    let mut v = Vec::new();
    v.push(10u32);
    v.push(20u32);
    v.push(30u32);
    truncate(&mut v, 5);
    assert!(v.len() == 3);
    truncate(&mut v, 1);
    assert!(v.len() == 1);
    assert!(v[0] == 10);
    clear(&mut v);
    assert!(is_empty(&v));
    clear(&mut v);
    truncate(&mut v, 0);
    assert!(is_empty(&v));
}

#[verify::test]
pub fn check_retain_state() {
    let mut v = Vec::new();
    v.push(10u32);
    v.push(20u32);
    v.push(30u32);
    v.push(40u32);
    let mut keep = false;
    retain(&mut v, move |_| {
        keep = !keep;
        keep
    });
    assert!(v.len() == 2);
    assert!(v[0] == 10);
    assert!(v[1] == 30);
}

// Deliberately asymmetric: detects reversal of the native dedup callback arguments.
pub struct DirectionalEq {
    pub key: u32,
}

impl PartialEq for DirectionalEq {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key || (self.key == 2 && other.key == 1)
    }
}

#[verify::test]
pub fn check_dedup_comparison_direction() {
    let mut v = Vec::new();
    v.push(DirectionalEq { key: 1 });
    v.push(DirectionalEq { key: 2 });
    v.push(DirectionalEq { key: 3 });
    v.push(DirectionalEq { key: 2 });
    v.push(DirectionalEq { key: 1 });
    dedup(&mut v);
    assert!(v.len() == 4);
    assert!(v[0].key == 1);
    assert!(v[1].key == 3);
    assert!(v[2].key == 2);
    assert!(v[3].key == 1);
}

#[verify::test]
pub fn check_dedup_adjacent_only() {
    let mut v = Vec::new();
    v.push(1u32);
    v.push(1u32);
    v.push(2u32);
    v.push(2u32);
    v.push(1u32);
    dedup(&mut v);
    assert!(v.len() == 3);
    assert!(v[0] == 1);
    assert!(v[1] == 2);
    assert!(v[2] == 1);
}
