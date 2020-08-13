#![no_std]

#![deny(warnings)]

#[macro_use]
extern crate macro_attr;
#[macro_use]
extern crate components_arena;

mod widgets {
    use core::num::NonZeroU32;
    use components_arena::{Arena, Id, ComponentClassToken};

    macro_attr! {
        #[derive(Component!(index=u16, unique=NonZeroU32))]
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
            let mut arena = Arena::new();
            let root = arena.push(&mut token.0, |this| WidgetData {
                parent: None, next: this, last_child: None
            });
            Widgets { arena, root }
        }

        pub fn root(&self) -> Widget { Widget(self.root) }
    }

    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
    pub struct Widget(Id<WidgetData>);

    impl Widget {
        pub fn new(token: &mut WidgetsToken, widgets: &mut Widgets, parent: Widget) -> Widget {
            let widget = widgets.arena.push(&mut token.0, |this| WidgetData {
                parent: Some(parent.0), next: this, last_child: None
            });
            if let Some(prev) = widgets.arena.get_mut(parent.0).unwrap().last_child.replace(widget) {
                widgets.arena.get_mut(widget).unwrap().next = prev;
            }
            Widget(widget)
        }

        pub fn parent(self, widgets: &Widgets) -> Option<Widget> {
            widgets.arena.get(self.0).unwrap().parent.map(Widget)
        }
    }
}

use widgets::*;

fn main() {
    let token = &mut WidgetsToken::new().unwrap();
    let widgets = &mut Widgets::new(token);
    let widget = Widget::new(token, widgets, widgets.root());
    assert_eq!(widget.parent(widgets), Some(widgets.root()));
}
