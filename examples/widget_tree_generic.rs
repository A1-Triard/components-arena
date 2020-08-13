#![deny(warnings)]

#[macro_use]
extern crate derivative;
#[macro_use]
extern crate macro_attr;
#[macro_use]
extern crate components_arena;

mod widgets {
    use std::num::NonZeroU32;
    use components_arena::{Components, Id, ComponentsTokenMutex};

    macro_attr! {
        #[derive(Component!(index=u16, id=NonZeroU32, class=WidgetDataComponent))]
        struct WidgetData<T> {
            parent: Option<Id<WidgetData<T>>>,
            next: Id<WidgetData<T>>,
            last_child: Option<Id<WidgetData<T>>>,
            context: T
        }
    }

    static WIDGET: ComponentsTokenMutex<WidgetDataComponent> = ComponentsTokenMutex::new();

    pub struct Widgets<T> {
        arena: Components<WidgetData<T>>,
        root: Id<WidgetData<T>>,
    }

    impl<T> Widgets<T> {
        pub fn new(context: T) -> Self {
            let mut arena = Components::new();
            let root = arena.attach(&mut WIDGET.lock().unwrap(), |this| WidgetData {
                parent: None, next: this, last_child: None, context
            });
            Widgets { arena, root }
        }

        pub fn root(&self) -> Widget<T> { Widget(self.root) }
    }

    #[derive(Derivative)]
    #[derivative(Debug(bound=""), Copy(bound=""), Clone(bound=""), Eq(bound=""), PartialEq(bound=""))]
    #[derivative(Hash(bound=""), Ord(bound=""), PartialOrd(bound=""))]
    pub struct Widget<T>(Id<WidgetData<T>>);

    impl<T> Widget<T> {
        pub fn new(widgets: &mut Widgets<T>, parent: Widget<T>, context: T) -> Widget<T> {
            let widget = widgets.arena.attach(&mut WIDGET.lock().unwrap(), |this| WidgetData {
                parent: Some(parent.0), next: this, last_child: None, context
            });
            if let Some(prev) = widgets.arena.get_mut(parent.0).unwrap().last_child.replace(widget) {
                widgets.arena.get_mut(widget).unwrap().next = prev;
            }
            Widget(widget)
        }

        pub fn parent(self, widgets: &Widgets<T>) -> Option<Widget<T>> {
            widgets.arena.get(self.0).unwrap().parent.map(Widget)
        }

        pub fn context(self, widgets: &Widgets<T>) -> &T {
            &widgets.arena.get(self.0).unwrap().context
        }
    }
}

use widgets::*;

fn main() {
    let widgets = &mut Widgets::new(1u32);
    let widget = Widget::new(widgets, widgets.root(), 7u32);
    assert_eq!(widget.context(widgets), &7u32);
    assert_eq!(widget.parent(widgets), Some(widgets.root()));
}
