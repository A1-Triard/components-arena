#![deny(warnings)]

#[macro_use]
extern crate derivative;
#[macro_use]
extern crate macro_attr;
#[macro_use]
extern crate components_arena;

mod widgets {
    use components_arena::{Arena, Id, ComponentClassMutex};

    macro_attr! {
        #[derive(Component!(class=WidgetDataComponent))]
        struct WidgetData<T> {
            parent: Option<Id<WidgetData<T>>>,
            next: Id<WidgetData<T>>,
            last_child: Option<Id<WidgetData<T>>>,
            context: T
        }
    }

    static WIDGET: ComponentClassMutex<WidgetDataComponent> = ComponentClassMutex::new();

    pub struct Widgets<T> {
        arena: Arena<WidgetData<T>>,
        root: Id<WidgetData<T>>,
    }

    impl<T> Widgets<T> {
        pub fn new(context: T) -> Self {
            let mut arena = Arena::new(&mut WIDGET.lock().unwrap());
            let root = arena.insert(|this| (WidgetData {
                parent: None, next: this, last_child: None, context
            }, this));
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
            let widget = widgets.arena.insert(|this| (WidgetData {
                parent: Some(parent.0), next: this, last_child: None, context
            }, this));
            if let Some(prev) = widgets.arena[parent.0].last_child.replace(widget) {
                widgets.arena[widget].next = prev;
            }
            Widget(widget)
        }

        pub fn parent(self, widgets: &Widgets<T>) -> Option<Widget<T>> {
            widgets.arena[self.0].parent.map(Widget)
        }

        pub fn context(self, widgets: &Widgets<T>) -> &T {
            &widgets.arena[self.0].context
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
