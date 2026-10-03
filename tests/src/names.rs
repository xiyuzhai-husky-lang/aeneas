//@ [!lean] skip

#![feature(register_tool)]
#![register_tool(verify)]

struct Struct {
    name: String,
}

mod clause {
    pub struct Clause {
        pub value: u32,
    }
}

// The parameter must not shadow the namespace in the return type or body.
pub fn namespace_collision(clause: clause::Clause) -> clause::Clause {
    clause::Clause {
        value: clause.value,
    }
}

pub struct State {
    pub ok: bool,
    pub fail: bool,
    pub panic: bool,
}

impl State {
    // These definitions are in State's namespace, where its fields can hide
    // the opened Result.ok, Result.fail, and Error.panic constructors.
    pub fn read(&self) -> bool {
        self.ok
    }

    pub fn check(&self) {
        assert!(self.ok);
    }

    pub fn fail_if_set(&self) -> bool {
        if self.fail {
            panic!();
        }
        self.ok
    }
}

#[verify::test]
pub fn name_collisions_work() {
    let value = namespace_collision(clause::Clause { value: 7 });
    assert!(value.value == 7);
    let state = State {
        ok: true,
        fail: false,
        panic: false,
    };
    assert!(state.read());
    assert!(state.fail_if_set());
    state.check();
}
