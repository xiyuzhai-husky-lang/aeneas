//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub fn clone32(x: &f32) -> f32 {
    x.clone()
}
pub fn default32() -> f32 {
    f32::default()
}
pub fn partial_cmp32(x: f32, y: f32) -> Option<std::cmp::Ordering> {
    x.partial_cmp(&y)
}
pub fn infinity32() -> f32 {
    f32::INFINITY
}

pub fn clone64(x: &f64) -> f64 {
    x.clone()
}
pub fn default64() -> f64 {
    f64::default()
}
pub fn partial_cmp64(x: f64, y: f64) -> Option<std::cmp::Ordering> {
    x.partial_cmp(&y)
}
pub fn infinity64() -> f64 {
    f64::INFINITY
}
