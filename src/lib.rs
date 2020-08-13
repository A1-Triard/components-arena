#![deny(warnings)]
#![feature(const_fn)]

#![cfg_attr(not(feature="std"), no_std)]
#[cfg(not(feature="std"))]
extern crate alloc;
#[cfg(not(feature="std"))]
pub(crate) mod std {
    pub use core::*;
    pub use ::alloc::vec;
}

#[macro_use]
extern crate derivative;

use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;
use std::hash::Hash;
use std::hint::unreachable_unchecked;
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};
use std::sync::atomic::{AtomicBool, Ordering};
use std::vec::Vec;
#[cfg(feature="std")]
use once_cell::sync::{self};
#[cfg(feature="std")]
use std::sync::Mutex;
#[cfg(feature="std")]
use std::ops::Deref;

/// An implementor of the `ComponentId` trait
/// can be used as a component actual id type.
///
/// In the generational arena approach every component has an `Id`
/// consisting of two parts: index, and actual id.
/// First part, index, is distinct for all alive components,
/// but second one, id, is distinct for all components
/// created during application run time.
///
/// # Safety
///
/// Safe implementation should purely, correctly and consistently implement
/// `Clone`, `PartialEq`, `Eq`, `Hash`, `PartialOrd`, and `Ord` traits.
///
/// The `inc` function should be pure, and produce
/// a serie of distinct values when applied cycely to `None`.
pub unsafe trait ComponentId: Debug + Copy + Eq + Hash + Ord {
    /// Takes last generated id and returns next free one.
    fn inc(this: Option<Self>) -> Option<Self>;
}

unsafe impl ComponentId for NonZeroU8 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentId for NonZeroU16 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentId for NonZeroU32 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentId for NonZeroU64 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentId for NonZeroU128 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentId for NonZeroUsize {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

/// An implementor of the `ComponentIndex` trait
/// can be used as an index part type of a component `Id`.
///
/// In the generational arena approach every component has an `Id`
/// consisting of two parts: index, and actual id.
/// First part, index, is distinct for all alive components,
/// but second one, id, is distinct for all components
/// created during application run time.
///
/// # Safety
///
/// Safe implementation should purely, correctly and consistently implement
/// `Clone`, `PartialEq`, `Eq`, `Hash`, `PartialOrd`, and `Ord` traits.
///
/// The `TryInto<usize>` and `TryFrom<usize>` implementaions should be pure,
/// and if `try_from(n)` is `Ok(x)` then `try_into(x)` should be `Ok(n)`.
pub unsafe trait ComponentIndex: Debug + Copy + Eq + Hash + Ord + TryInto<usize> + TryFrom<usize> { }

unsafe impl ComponentIndex for u8 { }

unsafe impl ComponentIndex for u16 { }

unsafe impl ComponentIndex for u32 { }

unsafe impl ComponentIndex for u64 { }

unsafe impl ComponentIndex for u128 { }

unsafe impl ComponentIndex for usize { }

/// The return type of the `ComponentClass::lock` function.
///
/// The `ComponentClass::component_token_lock` function
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
/// common non-generic synthetic uninhabited type `XComponent` and implement
/// `ComponentClass` for this synthetic type.
///
/// # Safety
///
/// Correct safe implementation should return reference to the one and same
/// `ComponentClassLock` instance from the `lock` function.
///
/// Also it should be garanteed that no other `ComponentClass` implementation
/// returns same `ComponentClassLock` instance.
///
/// This requirements can be easaly satisfied with private static:
///
/// ```rust
/// unsafe impl ComponentClass for MyComponent {
///     fn lock() -> &'static ComponentClassLock {
///         static CLASS_LOCK: ComponentClassLock = ComponentTokenLock::new();
///         &CLASS_LOCK
///     }
///     // ...
/// }
/// ```
pub unsafe trait ComponentClass {
    /// First part of compound component id, distincting all alive components.
    type Index: ComponentIndex;

    /// Second part of compound component id, distincting all components
    /// created during application run time.
    type Id: ComponentId;

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

/// Component handle.
///
/// Distinct components are guaranteed to have distinct handles.
#[derive(Derivative)]
#[derivative(Debug(bound=""), Copy(bound=""), Clone(bound=""), Eq(bound=""), PartialEq(bound=""))]
#[derivative(Hash(bound=""), Ord(bound=""), PartialOrd(bound=""))]
pub struct Id<C: Component> {
    index: <<C as Component>::Class as ComponentClass>::Index,
    id: <<C as Component>::Class as ComponentClass>::Id,
}

/// Unordered container with random access.
///
/// Prevents incorrect access through deleted or foreign `Id`.
#[derive(Debug)]
pub struct Arena<C: Component> {
    items: Vec<Option<(<<C as Component>::Class as ComponentClass>::Id, C)>>,
    vacancies: Vec<<<C as Component>::Class as ComponentClass>::Index>,
}

/// Component class static shared data.
///
/// In the `std` environment can be stored inside static `ComponentClassMutex`:
///
/// ```rust
/// static MY_COMPONENT: ComponentClassMutex<MyComponent = ComponentClassMutex::new();
///
/// // ...
///
/// let id = arena.push(&mut MY_COMPONENT.lock().unwrap() /*, ... */);
/// ```
///
/// In `no_std` environment a custom solution should be used to store `ComponentClassToken`.
pub struct ComponentClassToken<C: ComponentClass>(Option<C::Id>);

impl<C: ComponentClass> ComponentClassToken<C> {
    pub fn new() -> Option<ComponentClassToken<C>> {
        let lock = C::lock();
        if lock.0.compare_and_swap(false, true, Ordering::Relaxed) {
            None
        } else {
            Some(ComponentClassToken(None))
        }
    }
}

impl<C: Component> Arena<C> {
    pub fn new() -> Self {
        Arena { items: Vec::new(), vacancies: Vec::new() }
    }

    pub fn push(&mut self, token: &mut ComponentClassToken<C::Class>, component: impl FnOnce(Id<C>) -> C) -> Id<C> {
        let id = <<C as Component>::Class as ComponentClass>::Id::inc(token.0).expect("component ids exhausted");
        token.0 = Some(id);
        if let Some(index) = self.vacancies.pop() {
            let index_id = Id { index, id };
            let item = (id, component(index_id));
            let index_as_usize = index.try_into().unwrap_or_else(|_| unsafe { unreachable_unchecked() });
            let none = self.items[index_as_usize].replace(item);
            debug_assert!(none.is_none());
            index_id
        } else {
            let index = self.items.len().try_into().unwrap_or_else(|_| panic!("component indexes exhausted"));
            let index_id = Id { index, id };
            let item = (id, component(index_id));
            self.items.push(Some(item));
            index_id
        }
    }

    #[must_use]
    pub fn pop(&mut self, id: Id<C>) -> Option<C> {
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| unsafe { unreachable_unchecked() });
        if self.items.len() <= index_as_usize { return None; }
        if let Some((item_id, component)) = self.items[index_as_usize].take() {
            if item_id == id.id {
                self.vacancies.push(id.index);
                Some(component)
            } else {
                let none = self.items[index_as_usize].replace((item_id, component));
                debug_assert!(none.is_none());
                None
            }
        } else {
            None
        }
    }

    pub fn get(&self, id: Id<C>) -> Option<&C> {
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| unsafe { unreachable_unchecked() });
        if self.items.len() <= index_as_usize { return None; }
        self.items[index_as_usize].as_ref().and_then(|&(item_id, ref component)| {
            if item_id == id.id {
                Some(component)
            } else {
                None
            }
        })
    }

    pub fn get_mut(&mut self, id: Id<C>) -> Option<&mut C> {
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| unsafe { unreachable_unchecked() });
        if self.items.len() <= index_as_usize { return None; }
        self.items[index_as_usize].as_mut().and_then(|&mut (item_id, ref mut component)| {
            if item_id == id.id {
                Some(component)
            } else {
                None
            }
        })
    }
}

impl<C: Component> Default for Arena<C> {
    fn default() -> Self { Arena::new() }
}

#[cfg(feature="std")]
pub struct ComponentClassMutex<C: ComponentClass>(sync::Lazy<Mutex<ComponentClassToken<C>>>);

#[cfg(feature="std")]
impl<C: ComponentClass> ComponentClassMutex<C> {
    pub const fn new() -> Self {
        ComponentClassMutex(sync::Lazy::new(|| Mutex::new(
            ComponentClassToken::new().unwrap_or_else(|| unsafe { unreachable_unchecked() })
        )))
    }
}

#[cfg(feature="std")]
impl<C: ComponentClass> Deref for ComponentClassMutex<C> {
    type Target = Mutex<ComponentClassToken<C>>;

    fn deref(&self) -> &Self::Target { self.0.deref() }
}

#[macro_export]
macro_rules! Component {
    ((index=$index:ty, id=$id:ty, class=$class:ident)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, id=$id:ty)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, index=$index:ty, class=$class:ident)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, class=$class:ident, index=$index:ty)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, id=$id:ty)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, id=$id:ty, index=$index:ty)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, id=$id:ty, class=$class:ident)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, id=$id:ty)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, index=$index:ty, class=$class:ident)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, class=$class:ident, index=$index:ty)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, id=$id:ty)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, id=$id:ty, index=$index:ty)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, id=$id:ty, class=$class:ident)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, id=$id:ty)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, index=$index:ty, class=$class:ident)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, class=$class:ident, index=$index:ty)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, id=$id:ty)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, id=$id:ty, index=$index:ty)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, index=$index:ty)
        $(pub $((crate))?)? enum $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name, $id, $index
        }
    };
    ((index=$index:ty, id=$id:ty)
        $(pub $((crate))?)? enum $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name, $id, $index
        }
    };
    ((index=$index:ty, id=$id:ty, class=$class:ident)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, id=$id:ty)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, index=$index:ty, class=$class:ident)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, class=$class:ident, index=$index:ty)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, id=$id:ty)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, id=$id:ty, index=$index:ty)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, id=$id:ty, class=$class:ident)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, id=$id:ty)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, index=$index:ty, class=$class:ident)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, class=$class:ident, index=$index:ty)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, id=$id:ty)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, id=$id:ty, index=$index:ty)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, id=$id:ty, class=$class:ident)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, id=$id:ty)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, index=$index:ty, class=$class:ident)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, class=$class:ident, index=$index:ty)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, id=$id:ty)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, id=$id:ty, index=$index:ty)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $id, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((id=$id:ty, index=$index:ty)
        $(pub $((crate))?)? struct $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name, $id, $index
        }
    };
    ((index=$index:ty, id=$id:ty)
        $(pub $((crate))?)? struct $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name, $id, $index
        }
    };
    (@impl $name:ident, $id:ty, $index:ty) => {
        unsafe impl $crate::ComponentClass for $name {
            type Id = $id;
            type Index = $index;
            fn lock() -> &'static $crate::ComponentClassLock {
                static CLASS_LOCK: $crate::ComponentClassLock = $crate::ComponentClassLock::new();
                &CLASS_LOCK
            }
        }
        impl $crate::Component for $name {
            type Class = Self;
        }
    };
    (@impl ($($p:tt $($c:tt)?)?) $name:ident, $id:ty, $index:ty, $class:ident, < $g:tt >, < $r:tt >) => {
        $($p $($c)?)? enum $class { }
        unsafe impl $crate::ComponentClass for $class {
            type Id = $id;
            type Index = $index;
            fn lock() -> &'static $crate::ComponentClassLock {
                static CLASS_LOCK: $crate::ComponentClassLock = $crate::ComponentClassLock::new();
                &CLASS_LOCK
            }
        }
        impl< $g > $crate::Component for $name < $r > {
            type Class = $class;
        }
    };
}
