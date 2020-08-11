#![feature(once_cell)]

#[macro_use]
extern crate macro_attr;
#[macro_use]
extern crate components_arena;

use std::num::NonZeroU32;
use components_arena::{Components, Id};

macro_attr! {
    #[derive(Component!(TOKEN_LOCK=WIDGET_LOCK, TOKEN=WIDGET, Index=u16, Id=NonZeroU32))]
    struct Widget {
        parent: Option<Id<Widget>>,
        next: Id<Widget>,
        last_child: Option<Id<Widget>>,
    }
}

struct Widgets {
    arena: Components<Widget>,
}

impl Widgets {
    fn new() -> Widgets {
        Widgets {
            arena: <Components<Widget>>::new()
        }
    }
}

fn main() {
    Widgets::new();
}
