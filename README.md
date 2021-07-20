# components-arena

Strong-typed arena.
Simple library for creating complex domain-specific self-referential data structures.

This arena does not use generations approach in a strict sense,
but it uses some similar technique for avoiding the ABA effect.

## Example: circular linked list

```rust
use std::mem::replace;
use macro_attr_2018::macro_attr;
use components_arena::{Id, Arena, Component, ComponentClassMutex};

macro_attr! {
    #[derive(Component!)]
    struct Node {
        next: Id<Node>,
        data: (),
    }
}

static NODE: ComponentClassMutex<Node> = ComponentClassMutex::new();

struct List {
    last: Option<Id<Node>>,
    nodes: Arena<Node>,
}

impl List {
    fn new() -> Self {
        List { last: None, nodes: Arena::new(&mut NODE.lock().unwrap()) }
    }

    fn push(&mut self, data: () -> Id<Node> {
        let id = self.nodes.insert(|id| (Node { next: id, data }, id));
        if let Some(last) = self.last {
            self.nodes[id].next = replace(&mut self.nodes[last].next, id);
        } else {
            self.last = Some(id);
        }
        id
    }
}
```
