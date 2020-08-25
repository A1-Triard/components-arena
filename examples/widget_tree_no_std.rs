#![no_std]

#![deny(warnings)]

#[macro_use]
extern crate macro_attr;
#[macro_use]
extern crate components_arena;

mod widgets {
    use components_arena::{Arena, Id, ComponentClassToken};

    macro_attr! {
        #[derive(Component!)]
        struct WidgetData {
            parent: Option<Id<WidgetData>>,
            next: Id<WidgetData>,
            last_child: Option<Id<WidgetData>>,
        }
    }

    pub struct Widgets {
        arena: Arena<WidgetData>,
        root: Id<WidgetData>,
    }

    pub struct WidgetsToken(ComponentClassToken<WidgetData>);

    impl WidgetsToken {
        pub fn new() -> Option<WidgetsToken> { ComponentClassToken::new().map(WidgetsToken) }
    }

    impl Widgets {
        pub fn new(token: &mut WidgetsToken) -> Widgets {
            let mut arena = Arena::new(&mut token.0);
            let root = arena.insert(|this| WidgetData {
                parent: None, next: this, last_child: None
            });
            Widgets { arena, root }
        }

        pub fn root(&self) -> Widget { Widget(self.root) }
    }

    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
    pub struct Widget(Id<WidgetData>);

    impl Widget {
        pub fn new(widgets: &mut Widgets, parent: Widget) -> Widget {
            let widget = widgets.arena.insert(|this| WidgetData {
                parent: Some(parent.0), next: this, last_child: None
            });
            if let Some(prev) = widgets.arena[parent.0].last_child.replace(widget) {
                widgets.arena[widget].next = prev;
            }
            Widget(widget)
        }

        pub fn parent(self, widgets: &Widgets) -> Option<Widget> {
            widgets.arena[self.0].parent.map(Widget)
        }
    }
}

use widgets::*;

fn main() {
    let token = &mut WidgetsToken::new().unwrap();
    let widgets = &mut Widgets::new(token);
    let widget = Widget::new(widgets, widgets.root());
    assert_eq!(widget.parent(widgets), Some(widgets.root()));
}
