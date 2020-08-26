#![no_std]

#![deny(warnings)]
#![allow(dead_code)]

#[macro_use]
extern crate macro_attr;
#[macro_use]
extern crate components_arena;

mod widget_tree {
    use components_arena::{Arena, Id, ComponentClassToken};

    macro_attr! {
        #[derive(Component!)]
        struct WidgetNode {
            parent: Option<Id<WidgetNode>>,
            next: Id<WidgetNode>,
            last_child: Option<Id<WidgetNode>>,
        }
    }

    pub struct WidgetTree {
        arena: Arena<WidgetNode>,
        root: Id<WidgetNode>,
    }

    pub struct WidgetTreeToken(ComponentClassToken<WidgetNode>);

    impl WidgetTreeToken {
        pub fn new() -> Option<WidgetTreeToken> { ComponentClassToken::new().map(WidgetTreeToken) }
    }

    impl WidgetTree {
        pub fn new(token: &mut WidgetTreeToken) -> WidgetTree {
            let mut arena = Arena::new(&mut token.0);
            let root = arena.insert(|this| (WidgetNode {
                parent: None, next: this, last_child: None
            }, this));
            WidgetTree { arena, root }
        }

        pub fn root(&self) -> Widget { Widget(self.root) }
    }

    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
    pub struct Widget(Id<WidgetNode>);

    impl Widget {
        pub fn new(tree: &mut WidgetTree, parent: Widget) -> Widget {
            let widget = tree.arena.insert(|this| (WidgetNode {
                parent: Some(parent.0), next: this, last_child: None
            }, this));
            if let Some(prev) = tree.arena[parent.0].last_child.replace(widget) {
                tree.arena[widget].next = prev;
            }
            Widget(widget)
        }

        pub fn drop(self, tree: &mut WidgetTree) {
            tree.arena.remove(self.0);
        }

        pub fn parent(self, tree: &WidgetTree) -> Option<Widget> {
            tree.arena[self.0].parent.map(Widget)
        }
    }
}

use widget_tree::*;

fn main() {
    let token = &mut WidgetTreeToken::new().unwrap();
    let tree = &mut WidgetTree::new(token);
    let widget = Widget::new(tree, tree.root());
    assert_eq!(widget.parent(tree), Some(tree.root()));
}
