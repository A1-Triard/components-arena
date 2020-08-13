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

/// An implementor of the `ComponentUnique` trait
/// can be used as a unique part type of `Id`.
///
/// In the generational arena approach every component has an id
/// consisting of two parts: index, and actual unique id.
/// First part, index, is distinct for all alive components,
/// but second one, unique, is distinct for all components
/// created during application run time.
///
/// # Safety
///
/// Safe implementation should purely, correctly and consistently implement
/// `Clone`, `PartialEq`, `Eq`, `Hash`, `PartialOrd`, and `Ord` traits.
///
/// The `inc` function should be pure, and produce
/// a serie of distinct values when applied cycely to `None`.
pub unsafe trait ComponentUnique: Debug + Copy + Eq + Hash + Ord {
    /// Takes last generated value and returns next free one.
    fn inc(this: Option<Self>) -> Option<Self>;
}

unsafe impl ComponentUnique for NonZeroU8 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentUnique for NonZeroU16 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentUnique for NonZeroU32 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentUnique for NonZeroU64 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentUnique for NonZeroU128 {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

unsafe impl ComponentUnique for NonZeroUsize {
    fn inc(this: Option<Self>) -> Option<Self> {
        Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0)
    }
}

/// An implementor of the `ComponentIndex` trait
/// can be used as an index part type of `Id`.
///
/// In the generational arena approach every component has an id
/// consisting of two parts: index, and actual unique id.
/// First part, index, is distinct for all alive components,
/// but second one, unique, is distinct for all components
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
///         static CLASS_LOCK: ComponentClassLock = ComponentClassLock::new();
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
    type Unique: ComponentUnique;

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
    index: <<C as Component>::Class as ComponentClass>::Index,
    unique: <<C as Component>::Class as ComponentClass>::Unique,
}

/// Unordered container with random access.
///
/// Prevents incorrect access through deleted or foreign `Id`.
#[derive(Debug)]
pub struct Arena<C: Component> {
    items: Vec<Option<(<<C as Component>::Class as ComponentClass>::Unique, C)>>,
    vacancies: Vec<<<C as Component>::Class as ComponentClass>::Index>,
}

/// Component class static shared data.
///
/// In the no-`no_std` environment it can be stored inside static `ComponentClassMutex`:
///
/// ```rust
/// static MY_COMPONENT: ComponentClassMutex<MyComponent = ComponentClassMutex::new();
///
/// // ...
///
/// let id = arena.push(&mut MY_COMPONENT.lock().unwrap() /*, ... */);
/// ```
///
/// In the `no_std` environment a custom solution should be used to store `ComponentClassToken`.
pub struct ComponentClassToken<C: ComponentClass>(Option<C::Unique>);

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
        let unique = <<C as Component>::Class as ComponentClass>::Unique::inc(token.0).expect("component ids exhausted");
        token.0 = Some(unique);
        if let Some(index) = self.vacancies.pop() {
            let id = Id { index, unique };
            let item = (unique, component(id));
            let index_as_usize = index.try_into().unwrap_or_else(|_| unsafe { unreachable_unchecked() });
            let none = self.items[index_as_usize].replace(item);
            debug_assert!(none.is_none());
            id
        } else {
            let index = self.items.len().try_into().unwrap_or_else(|_| panic!("component indexes exhausted"));
            let id = Id { index, unique };
            let item = (unique, component(id));
            self.items.push(Some(item));
            id
        }
    }

    #[must_use]
    pub fn pop(&mut self, id: Id<C>) -> Option<C> {
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| unsafe { unreachable_unchecked() });
        if self.items.len() <= index_as_usize { return None; }
        self.items[index_as_usize].take().and_then(|(unique, component)| {
            if unique == id.unique {
                self.vacancies.push(id.index);
                Some(component)
            } else {
                let none = self.items[index_as_usize].replace((unique, component));
                debug_assert!(none.is_none());
                None
            }
        })
    }

    pub fn get(&self, id: Id<C>) -> Option<&C> {
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| unsafe { unreachable_unchecked() });
        if self.items.len() <= index_as_usize { return None; }
        self.items[index_as_usize].as_ref().and_then(|&(unique, ref component)| {
            if unique == id.unique {
                Some(component)
            } else {
                None
            }
        })
    }

    pub fn get_mut(&mut self, id: Id<C>) -> Option<&mut C> {
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| unsafe { unreachable_unchecked() });
        if self.items.len() <= index_as_usize { return None; }
        self.items[index_as_usize].as_mut().and_then(|&mut (unique, ref mut component)| {
            if unique == id.unique {
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

/// Helps to store `ComponentClassToken` in a static.
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

/// [Macro attribute](https://crates.io/crates/macro-attr) for deriving `Component` trait.
#[macro_export]
macro_rules! Component {
    ((index=$index:ty, unique=$unique:ty, class=$class:ident)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, unique=$unique:ty)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, index=$index:ty, class=$class:ident)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, class=$class:ident, index=$index:ty)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, unique=$unique:ty)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, unique=$unique:ty, index=$index:ty)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, unique=$unique:ty, class=$class:ident)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, unique=$unique:ty)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, index=$index:ty, class=$class:ident)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, class=$class:ident, index=$index:ty)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, unique=$unique:ty)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, unique=$unique:ty, index=$index:ty)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, unique=$unique:ty, class=$class:ident)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, unique=$unique:ty)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, index=$index:ty, class=$class:ident)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, class=$class:ident, index=$index:ty)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, unique=$unique:ty)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, unique=$unique:ty, index=$index:ty)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, index=$index:ty)
        $(pub $((crate))?)? enum $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name, $unique, $index
        }
    };
    ((index=$index:ty, unique=$unique:ty)
        $(pub $((crate))?)? enum $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name, $unique, $index
        }
    };
    ((index=$index:ty, unique=$unique:ty, class=$class:ident)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, unique=$unique:ty)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, index=$index:ty, class=$class:ident)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, class=$class:ident, index=$index:ty)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, unique=$unique:ty)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, unique=$unique:ty, index=$index:ty)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl () $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, unique=$unique:ty, class=$class:ident)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, unique=$unique:ty)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, index=$index:ty, class=$class:ident)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, class=$class:ident, index=$index:ty)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, unique=$unique:ty)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, unique=$unique:ty, index=$index:ty)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub(crate)) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, unique=$unique:ty, class=$class:ident)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((index=$index:ty, class=$class:ident, unique=$unique:ty)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, index=$index:ty, class=$class:ident)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, class=$class:ident, index=$index:ty)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, index=$index:ty, unique=$unique:ty)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((class=$class:ident, unique=$unique:ty, index=$index:ty)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $tail:tt ) => {
        Component! {
            @impl (pub) $name, $unique, $index, $class,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((unique=$unique:ty, index=$index:ty)
        $(pub $((crate))?)? struct $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name, $unique, $index
        }
    };
    ((index=$index:ty, unique=$unique:ty)
        $(pub $((crate))?)? struct $name:ident
        $tail:tt ) => {
        Component! {
            @impl $name, $unique, $index
        }
    };
    (@impl $name:ident, $unique:ty, $index:ty) => {
        unsafe impl $crate::ComponentClass for $name {
            type Unique = $unique;
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
    (@impl ($($p:tt $($c:tt)?)?) $name:ident, $unique:ty, $index:ty, $class:ident, < $g:tt >, < $r:tt >) => {
        $($p $($c)?)? enum $class { }
        unsafe impl $crate::ComponentClass for $class {
            type Unique = $unique;
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
