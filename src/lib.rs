#![deny(warnings)]
#![feature(const_fn)]
#![feature(try_reserve)]
#![feature(shrink_to)]

#![cfg_attr(not(feature="std"), no_std)]
#[cfg(not(feature="std"))]
extern crate alloc;
#[cfg(not(feature="std"))]
pub(crate) mod std {
    pub use core::*;
    pub use ::alloc::collections;
    pub use ::alloc::vec;
}

#[macro_use]
extern crate derivative;

use std::collections::TryReserveError;
use std::fmt::Debug;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::replace;
use std::num::{NonZeroUsize};
use std::ops::{Index, IndexMut};
use std::sync::atomic::{AtomicBool, Ordering};
use std::vec::Vec;
use either::{Either, Left, Right};
use rand::rngs::SmallRng;
use rand::{RngCore, SeedableRng};
#[cfg(feature="std")]
use once_cell::sync::{self};
#[cfg(feature="std")]
use std::sync::Mutex;
#[cfg(feature="std")]
use std::ops::Deref;

/// The return type of the `ComponentClass::lock` function.
///
/// The `ComponentClass::lock` function
/// is essential for components arena internal mechanic.
pub struct ComponentClassLock(AtomicBool);

impl ComponentClassLock {
    /// Creates new `ComponentClassLock` instance.
    ///
    /// The function is `const`, and can be used for static initialization.
    pub const fn new() -> Self { ComponentClassLock(AtomicBool::new(false)) }
}

impl Default for ComponentClassLock {
    fn default() -> Self { ComponentClassLock::new() }
}

/// An utility trait describing a specific component type.
///
/// Normaly for a non-generic component type
/// the component type itself implements `ComponentClass`.
///
/// For generic components it would be difficult to have
/// an own `ComponentClassLock` instance for every specialization because Rust
/// does not have "generic statics" feature.
///
/// So, if some component type `X` is generic, normally you should introduce
/// common non-generic uninhabited type `XComponent` and implement
/// `ComponentClass` for this synthetic type.
///
/// Correct implementation should return reference to the one and same
/// `ComponentClassLock` instance from the `lock` function.
///
/// Also it should be garanteed that no other `ComponentClass` implementation
/// returns same `ComponentClassLock` instance.
///
/// This requirements can be easaly satisfied with private static:
///
/// ```rust
/// use components_arena::{ComponentClass, ComponentClassLock};
///
/// struct MyComponent { /* ... */ }
/// impl ComponentClass for MyComponent {
///     fn lock() -> &'static ComponentClassLock {
///         static LOCK: ComponentClassLock = ComponentClassLock::new();
///         &LOCK
///     }
/// }
/// ```
pub trait ComponentClass {
    /// Essential for components arena internal mechanic.
    fn lock() -> &'static ComponentClassLock;
}

/// An implementor of the `Component` trait is a type, whose values can be placed into
/// `Arena` container.
pub trait Component {
    /// Component class.
    ///
    /// Normally it is `Self` for non-generic types, and
    /// non-generic synthetic uninhabited type for generic ones.
    type Class: ComponentClass;
}

/// `Arena` item handle.
#[derive(Derivative)]
#[derivative(Debug(bound=""), Copy(bound=""), Clone(bound=""), Eq(bound=""), PartialEq(bound=""))]
#[derivative(Hash(bound=""), Ord(bound=""), PartialOrd(bound=""))]
pub struct Id<C: Component> {
    index: usize,
    tag: NonZeroUsize,
    phantom: PhantomData<C>
}

/// Unordered container with random access.
#[derive(Debug)]
pub struct Arena<C: Component> {
    tag_rng: SmallRng,
    items: Vec<Either<Option<usize>, (NonZeroUsize, C)>>,
    vacancy: Option<usize>,
}

/// Component class static shared data.
///
/// In the no-`no_std` environment it can be stored inside static `ComponentClassMutex`:
///
/// ```rust
/// #[macro_use]
/// extern crate macro_attr;
/// #[macro_use]
/// extern crate components_arena;
/// use components_arena::{ComponentClassMutex, Arena};
///
/// macro_attr! {
///     #[derive(Component!)]
///     struct MyComponent { /* ... */ }
/// }
///
/// static MY_COMPONENT: ComponentClassMutex<MyComponent> = ComponentClassMutex::new();
///
/// // ...
///
/// fn main() {
///     let mut arena = Arena::new(&mut MY_COMPONENT.lock().unwrap());
///     let id = arena.push(|_| MyComponent { /* ... */ });
/// }
/// ```
///
/// In the `no_std` environment a custom solution should be used to store `ComponentClassToken`.
pub struct ComponentClassToken<C: ComponentClass> {
    tag_seed_rng: SmallRng,
    phantom: PhantomData<C>
}

impl<C: ComponentClass> ComponentClassToken<C> {
    /// Creates components shared data storage on first call for every component type `C`.
    /// All subsequent calls will return `None`.
    pub fn new() -> Option<ComponentClassToken<C>> {
        let lock = C::lock();
        if lock.0.compare_and_swap(false, true, Ordering::Relaxed) {
            None
        } else {
            Some(ComponentClassToken { tag_seed_rng: SmallRng::seed_from_u64(42), phantom: PhantomData })
        }
    }
}

impl<C: Component> Arena<C> {
    pub fn new(class: &mut ComponentClassToken<C::Class>) -> Self {
        Arena {
            tag_rng: SmallRng::seed_from_u64(class.tag_seed_rng.next_u64()),
            items: Vec::new(),
            vacancy: None
        }
    }

    pub fn with_capacity(capacity: usize, class: &mut ComponentClassToken<C::Class>) -> Self {
        Arena {
            tag_rng: SmallRng::seed_from_u64(class.tag_seed_rng.next_u64()),
            items: Vec::with_capacity(capacity),
            vacancy: None
        }
    }

    pub fn capacity(&self) -> usize { self.items.capacity() }

    pub fn len(&self) -> usize { self.items.len() }

    pub fn reserve(&mut self, additional: usize) { self.items.reserve(additional) }

    pub fn reserve_exact(&mut self, additional: usize) { self.items.reserve_exact(additional) }

    pub fn shrink_to(&mut self, min_capacity: usize) { self.items.shrink_to(min_capacity) }

    pub fn shrink_to_fit(&mut self) { self.items.shrink_to_fit() }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.items.try_reserve(additional)
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.items.try_reserve_exact(additional)
    }

    pub fn push(&mut self, component: impl FnOnce(Id<C>) -> C) -> Id<C> {
        let mut tag = 0usize.to_le_bytes();
        self.tag_rng.fill_bytes(&mut tag[..]);
        let tag = NonZeroUsize::new(usize::from_le_bytes(tag)).unwrap_or(unsafe { NonZeroUsize::new_unchecked(43) });
        if let Some(index) = self.vacancy {
            let id = Id { index, tag, phantom: PhantomData };
            let item = (tag, component(id));
            self.vacancy = replace(&mut self.items[index], Right(item)).left()
                .unwrap_or_else(|| unsafe { unreachable_unchecked() });
            id
        } else {
            let index = self.items.len();
            let id = Id { index, tag, phantom: PhantomData };
            let item = (tag, component(id));
            self.items.push(Right(item));
            id
        }
    }

    /// Removes component with provided id.
    ///
    /// The arena tries to detect invalid provided id (i. e. foreign, or previously dropped),
    /// and panics if such detection hits. But it is important to pay respect to the fact
    /// there is small probability that invalid id will not be intercepted.
    #[must_use]
    pub fn pop(&mut self, id: Id<C>) -> C {
        match replace(&mut self.items[id.index], Left(self.vacancy)) {
            Left(vacancy) => {
                self.items[id.index] = Left(vacancy);
                panic!("invalid id");
            },
            Right((tag, component)) => {
                if tag == id.tag {
                    self.vacancy = Some(id.index);
                    component
                } else {
                    self.items[id.index] = Right((tag, component));
                    panic!("invalid id");
                }
            }
        }
    }
}

impl<C: Component> Index<Id<C>> for Arena<C> {
    type Output = C;

    fn index(&self, id: Id<C>) -> &C {
        let &(tag, ref component) = self.items[id.index].as_ref().right().expect("invalid id");
        if tag != id.tag { panic!("invalid id"); }
        component
    }
}

impl<C: Component> IndexMut<Id<C>> for Arena<C> {
    fn index_mut(&mut self, id: Id<C>) -> &mut C {
        let &mut (tag, ref mut component) = self.items[id.index].as_mut().right().expect("invalid id");
        if tag != id.tag { panic!("invalid id"); }
        component
    }
}

/// Helps to store `ComponentClassToken` in a static.
#[cfg(feature="std")]
pub struct ComponentClassMutex<C: ComponentClass>(sync::Lazy<Mutex<ComponentClassToken<C>>>);

#[cfg(feature="std")]
impl<C: ComponentClass> ComponentClassMutex<C> {
    pub const fn new() -> Self {
        ComponentClassMutex(sync::Lazy::new(|| Mutex::new(
            ComponentClassToken::new().expect("component class token already crated")
        )))
    }
}

#[cfg(feature="std")]
impl<C: ComponentClass> Deref for ComponentClassMutex<C> {
    type Target = Mutex<ComponentClassToken<C>>;

    fn deref(&self) -> &Self::Target { self.0.deref() }
}

/// [Macro attribute](https://crates.io/crates/macro-attr) for deriving `Component` trait.
///
/// # Examples
///
/// ## Non-generic component
///
/// ```
/// #[macro_use]
/// extern crate macro_attr;
/// #[macro_use]
/// extern crate components_arena;
/// use components_arena::{ComponentClassMutex, Arena};
///
/// macro_attr! {
///     #[derive(Component!)]
///     struct Item { /* ... */ }
/// }
///
/// static ITEM: ComponentClassMutex<Item> = ComponentClassMutex::new();
///
/// // ...
///
/// fn main() {
///     let mut arena = Arena::new(&mut ITEM.lock().unwrap());
///     let id = arena.push(|_| Item { /* ... */ });
/// }
/// ```
///
/// ## Generic component
///
/// ```
/// #[macro_use]
/// extern crate macro_attr;
/// #[macro_use]
/// extern crate components_arena;
/// use components_arena::{ComponentClassMutex, Arena};
///
/// macro_attr! {
///     #[derive(Component!(class=ItemComponent))]
///     struct Item<T> {
///         context: T
///     }
/// }
///
/// static ITEM: ComponentClassMutex<ItemComponent> = ComponentClassMutex::new();
///
/// // ...
///
/// fn main() {
///     let mut arena_u8 = Arena::new(&mut ITEM.lock().unwrap());
///     let _ = arena_u8.push(|_| Item { context: 7u8 });
///
///     let mut arena_u32 = Arena::new(&mut ITEM.lock().unwrap());
///     let _ = arena_u32.push(|_| Item { context: 7u32 });
/// }
/// ```
#[macro_export]
macro_rules! Component {
    (()
        $(pub $((crate))?)? enum $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name
        }
    };
    (()
        $(pub $((crate))?)? struct $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name
        }
    };
    ((class=$class:ident)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    (@impl $name:ident) => {
        impl $crate::ComponentClass for $name {
            fn lock() -> &'static $crate::ComponentClassLock {
                static LOCK: $crate::ComponentClassLock = $crate::ComponentClassLock::new();
                &LOCK
            }
        }
        impl $crate::Component for $name {
            type Class = Self;
        }
    };
    (@impl ($($p:tt $($c:tt)?)?) $name:ident, $class:ident, < $g:tt >, < $r:tt >) => {
        $($p $($c)?)? enum $class { }
        impl $crate::ComponentClass for $class {
            fn lock() -> &'static $crate::ComponentClassLock {
                static LOCK: $crate::ComponentClassLock = $crate::ComponentClassLock::new();
                &LOCK
            }
        }
        impl< $g > $crate::Component for $name < $r > {
            type Class = $class;
        }
    };
}
