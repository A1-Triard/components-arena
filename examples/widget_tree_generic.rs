#![deny(warnings)]
#![allow(dead_code)]

#[macro_use]
extern crate derivative;
#[macro_use]
extern crate macro_attr;
#[macro_use]
extern crate components_arena;

mod widget_tree {
    use components_arena::{Arena, Id, ComponentClassMutex};

    macro_attr! {
        #[derive(Component!(class=WidgetNodeComponent))]
        struct WidgetNode<T> {
            parent: Option<Id<WidgetNode<T>>>,
            next: Id<WidgetNode<T>>,
            last_child: Option<Id<WidgetNode<T>>>,
            context: T
        }
    }

    static WIDGET_NODE: ComponentClassMutex<WidgetNodeComponent> = ComponentClassMutex::new();

    pub struct WidgetTree<T> {
        arena: Arena<WidgetNode<T>>,
        root: Id<WidgetNode<T>>,
    }

    impl<T> WidgetTree<T> {
        pub fn new(context: T) -> Self {
            let mut arena = Arena::new(&mut WIDGET_NODE.lock().unwrap());
            let root = arena.insert(|this| (WidgetNode {
                parent: None, next: this, last_child: None, context
            }, this));
            WidgetTree { arena, root }
        }

        pub fn root(&self) -> Widget<T> { Widget(self.root) }
    }

    #[derive(Derivative)]
    #[derivative(Debug(bound=""), Copy(bound=""), Clone(bound=""), Eq(bound=""), PartialEq(bound=""))]
    #[derivative(Hash(bound=""), Ord(bound=""), PartialOrd(bound=""))]
    pub struct Widget<T>(Id<WidgetNode<T>>);

    impl<T> Widget<T> {
        pub fn new(tree: &mut WidgetTree<T>, parent: Widget<T>, context: T) -> Widget<T> {
            let widget = tree.arena.insert(|this| (WidgetNode {
                parent: Some(parent.0), next: this, last_child: None, context
            }, this));
            if let Some(prev) = tree.arena[parent.0].last_child.replace(widget) {
                tree.arena[widget].next = prev;
            }
            Widget(widget)
        }

        pub fn drop(self, tree: &mut WidgetTree<T>) {
            tree.arena.remove(self.0);
        }

        pub fn parent(self, tree: &WidgetTree<T>) -> Option<Widget<T>> {
            tree.arena[self.0].parent.map(Widget)
        }

        pub fn context(self, tree: &WidgetTree<T>) -> &T {
            &tree.arena[self.0].context
        }
    }
}

use widget_tree::*;

fn main() {
    let tree = &mut WidgetTree::new(1u32);
    let widget = Widget::new(tree, tree.root(), 7u32);
    assert_eq!(widget.context(tree), &7u32);
    assert_eq!(widget.parent(tree), Some(tree.root()));
}
