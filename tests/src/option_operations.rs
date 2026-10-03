//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub fn map<T, U, F: FnOnce(T) -> U>(x: Option<T>, f: F) -> Option<U> {
    x.map(f)
}
pub fn map_or<T, U, F: FnOnce(T) -> U>(x: Option<T>, default: U, f: F) -> U {
    x.map_or(default, f)
}
pub fn cloned<T: Clone>(x: Option<&T>) -> Option<T> {
    x.cloned()
}
pub fn phantom<T>() -> std::marker::PhantomData<T> {
    Default::default()
}

#[verify::test]
pub fn check_map_branches() {
    assert!(map(None, |x: u32| 7 / x).is_none());
    assert!(map_or(None, 17, |x: u32| 7 / x) == 17);
    let offset = 10;
    assert!(map(Some(3), move |x| x + offset).unwrap() == 13);
    assert!(map_or(Some(7), 99, |x| x / 2) == 3);
}

pub struct CloneProbe {
    pub value: u32,
}
impl Clone for CloneProbe {
    fn clone(&self) -> Self {
        Self {
            value: self.value + 1,
        }
    }
}

#[verify::test]
pub fn check_clone_callback() {
    assert!(cloned::<CloneProbe>(None).is_none());
    let x = CloneProbe { value: 7 };
    assert!(cloned(Some(&x)).unwrap().value == 8);
}
