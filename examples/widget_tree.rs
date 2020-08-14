#![deny(warnings)]

#[macro_use]
extern crate macro_attr;
#[macro_use]
extern crate components_arena;

mod widgets {
    use std::num::{NonZeroU16, NonZeroU32};
    use components_arena::{Arena, Id, ComponentClassMutex};

    macro_attr! {
        #[derive(Component!(index=NonZeroU16, unique=NonZeroU32))]
        struct WidgetData {
            parent: Option<Id<WidgetData>>,
            next: Id<WidgetData>,
            last_child: Option<Id<WidgetData>>,
        }
    }

    static WIDGET: ComponentClassMutex<WidgetData> = ComponentClassMutex::new();

    pub struct Widgets {
        arena: Arena<WidgetData>,
        root: Id<WidgetData>,
    }

    impl Widgets {
        pub fn new() -> Widgets {
            let mut arena = Arena::new();
            let root = arena.push(&mut WIDGET.lock().unwrap(), |this| WidgetData {
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
            let widget = widgets.arena.push(&mut WIDGET.lock().unwrap(), |this| WidgetData {
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
    let widgets = &mut Widgets::new();
    let widget = Widget::new(widgets, widgets.root());
    assert_eq!(widget.parent(widgets), Some(widgets.root()));
}
