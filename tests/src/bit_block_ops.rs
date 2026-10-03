//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

use std::hash::{Hash, Hasher};

pub fn count_ones(x: u32) -> u32 {
    x.count_ones()
}

pub fn hash<H: Hasher>(x: u32, state: &mut H) {
    x.hash(state);
}

pub struct OverrideHasher {
    pub seen: u32,
    pub calls: u32,
}

impl Hasher for OverrideHasher {
    fn finish(&self) -> u64 {
        self.seen as u64
    }
    fn write(&mut self, _bytes: &[u8]) {
        self.seen = 0;
        self.calls += 100;
    }
    fn write_u32(&mut self, value: u32) {
        self.seen = value;
        self.calls += 1;
    }
}

#[verify::test]
pub fn check_count() {
    assert!(count_ones(0) == 0);
    assert!(count_ones(0xffff_ffff) == 32);
    assert!(count_ones(0x8000_0001) == 2);
    assert!(count_ones(0xaaaa_aaaa) == 16);
    assert!(count_ones(1) == 1);
}

#[verify::test]
pub fn check_hash_dispatch() {
    let mut h = OverrideHasher { seen: 0, calls: 0 };
    hash(0x1234_5678, &mut h);
    assert!(h.seen == 0x1234_5678);
    assert!(h.calls == 1);
    hash(0, &mut h);
    assert!(h.seen == 0);
    assert!(h.calls == 2);
}
