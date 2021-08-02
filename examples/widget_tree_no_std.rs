#![no_std]

#![deny(warnings)]
#![allow(dead_code)]

mod widget_tree {
    use macro_attr_2018::macro_attr;
    use components_arena::{Component, Arena, Id, NewtypeComponentId};

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

    impl WidgetTree {
        pub fn new() -> WidgetTree {
            let mut arena = Arena::new();
            let root = arena.insert(|this| (WidgetNode {
                parent: None, next: this, last_child: None
            }, this));
            WidgetTree { arena, root }
        }

        pub fn root(&self) -> Widget { Widget(self.root) }
    }

    macro_attr! {
        #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, NewtypeComponentId!)]
        pub struct Widget(Id<WidgetNode>);
    }

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
    let tree = &mut WidgetTree::new();
    let widget = Widget::new(tree, tree.root());
    assert_eq!(widget.parent(tree), Some(tree.root()));
}
