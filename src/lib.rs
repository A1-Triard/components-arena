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
use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;
use std::hash::Hash;
use std::mem::replace;
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};
use std::ops::{Index, IndexMut};
use std::sync::atomic::{AtomicBool, Ordering};
use std::vec::Vec;
use either::{Either, Left, Right};
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
/// The `ComponentUnique` correct implementation should behave
/// as primitive unsigned integer.
pub trait ComponentUnique: Debug + Copy + Eq + Hash + Ord + Default {
    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
    fn checked_sub(self, rhs: Self) -> Option<Self>;

    /// Calculates `self + rhs`. If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_add(self, d: Self) -> Self;

    /// Calculates `self + 1`. If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_inc(self) -> Self;
}

impl ComponentUnique for u8 {
    fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }

    fn overflowing_add(self, rhs: Self) -> Self { self.overflowing_add(rhs).0 }

    fn overflowing_inc(self) -> Self { self.overflowing_add(1).0 }
}

impl ComponentUnique for u16 {
    fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }

    fn overflowing_add(self, rhs: Self) -> Self { self.overflowing_add(rhs).0 }

    fn overflowing_inc(self) -> Self { self.overflowing_add(1).0 }
}

impl ComponentUnique for u32 {
    fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }

    fn overflowing_add(self, rhs: Self) -> Self { self.overflowing_add(rhs).0 }

    fn overflowing_inc(self) -> Self { self.overflowing_add(1).0 }
}

impl ComponentUnique for u64 {
    fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }

    fn overflowing_add(self, rhs: Self) -> Self { self.overflowing_add(rhs).0 }

    fn overflowing_inc(self) -> Self { self.overflowing_add(1).0 }
}

impl ComponentUnique for u128 {
    fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }

    fn overflowing_add(self, rhs: Self) -> Self { self.overflowing_add(rhs).0 }

    fn overflowing_inc(self) -> Self { self.overflowing_add(1).0 }
}

impl ComponentUnique for usize {
    fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }

    fn overflowing_add(self, rhs: Self) -> Self { self.overflowing_add(rhs).0 }

    fn overflowing_inc(self) -> Self { self.overflowing_add(1).0 }
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
/// The `from_usize` and `into_usize` functions should be pure,
/// and if `from_usize(n)` is `Some(x)` then `into_usize(x)` should be `Some(n)`.
pub trait ComponentIndex: Debug + Copy + Eq + Hash + Ord {
    fn from_usize(i: usize) -> Option<Self>;
    fn into_usize(self) -> Option<usize>;
}

impl ComponentIndex for NonZeroU8 {
    fn from_usize(i: usize) -> Option<Self> { Self::new(i.overflowing_add(1).0.try_into().ok()?) }
    fn into_usize(self) -> Option<usize> { Some(usize::try_from(self.get()).ok()?.overflowing_sub(1).0) }
}

impl ComponentIndex for NonZeroU16 {
    fn from_usize(i: usize) -> Option<Self> { Self::new(i.overflowing_add(1).0.try_into().ok()?) }
    fn into_usize(self) -> Option<usize> { Some(usize::try_from(self.get()).ok()?.overflowing_sub(1).0) }
}

impl ComponentIndex for NonZeroU32 {
    fn from_usize(i: usize) -> Option<Self> { Self::new(i.overflowing_add(1).0.try_into().ok()?) }
    fn into_usize(self) -> Option<usize> { Some(usize::try_from(self.get()).ok()?.overflowing_sub(1).0) }
}

impl ComponentIndex for NonZeroU64 {
    fn from_usize(i: usize) -> Option<Self> { Self::new(i.overflowing_add(1).0.try_into().ok()?) }
    fn into_usize(self) -> Option<usize> { Some(usize::try_from(self.get()).ok()?.overflowing_sub(1).0) }
}

impl ComponentIndex for NonZeroU128 {
    fn from_usize(i: usize) -> Option<Self> { Self::new(i.overflowing_add(1).0.try_into().ok()?) }
    fn into_usize(self) -> Option<usize> { Some(usize::try_from(self.get()).ok()?.overflowing_sub(1).0) }
}

impl ComponentIndex for NonZeroUsize {
    fn from_usize(i: usize) -> Option<Self> { Self::new(i.overflowing_add(1).0) }
    fn into_usize(self) -> Option<usize> { Some(self.get().overflowing_sub(1).0) }
}

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
///         static CLASS_LOCK: ComponentClassLock = ComponentClassLock::new();
///         &CLASS_LOCK
///     }
///
///     type Index = u32;
///     type Unique = std::num::NonZeroU64;
/// }
/// ```
pub trait ComponentClass {
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
    items: Vec<Either<
        Option<<<C as Component>::Class as ComponentClass>::Index>,
        (<<C as Component>::Class as ComponentClass>::Unique, C)
    >>,
    vacancy: Option<<<C as Component>::Class as ComponentClass>::Index>,
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
/// use std::num::NonZeroU64;
/// use components_arena::{ComponentClassMutex, Arena};
///
/// macro_attr! {
///     #[derive(Component!(index=u32, unique=NonZeroU64))]
///     struct MyComponent { /* ... */ }
/// }
///
/// static MY_COMPONENT: ComponentClassMutex<MyComponent> = ComponentClassMutex::new();
///
/// // ...
///
/// fn main() {
///     let mut arena = Arena::new();
///     let id = arena.push(&mut MY_COMPONENT.lock().unwrap(), |_| MyComponent { /* ... */ });
/// }
/// ```
///
/// In the `no_std` environment a custom solution should be used to store `ComponentClassToken`.
pub struct ComponentClassToken<C: ComponentClass> {
    next_unique: C::Unique,
    unique_base: C::Unique,
}

impl<C: ComponentClass> ComponentClassToken<C> {
    pub fn new() -> Option<ComponentClassToken<C>> {
        let lock = C::lock();
        if lock.0.compare_and_swap(false, true, Ordering::Relaxed) {
            None
        } else {
            Some(ComponentClassToken {
                next_unique: Default::default(),
                unique_base: Default::default()
            })
        }
    }
}

impl<C: Component> Arena<C> {
    pub fn new() -> Self {
        Arena { items: Vec::new(), vacancy: None }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Arena { items: Vec::with_capacity(capacity), vacancy: None }
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

    pub fn no_broken_id(&mut self) {
    }

    pub fn push(&mut self, token: &mut ComponentClassToken<C::Class>, component: impl FnOnce(Id<C>) -> C) -> Id<C> {
        let unique = token.next_unique;
        token.next_unique = unique.overflowing_inc();
        if token.next_unique == Default::default() { panic!("component uniques exhausted"); }
        let unique = unique.overflowing_add(token.unique_base);
        if let Some(index) = self.vacancy {
            let id = Id { index, unique };
            let item = (unique, component(id));
            let index_as_usize = index.into_usize().expect("invalid ComponentIndex");
            self.vacancy = replace(&mut self.items[index_as_usize], Right(item)).left().expect("Arena::push logic error");
            id
        } else {
            let index = <<C as Component>::Class as ComponentClass>::Index::from_usize(self.items.len())
                .expect("component indexes exhausted");
            let id = Id { index, unique };
            let item = (unique, component(id));
            self.items.push(Right(item));
            id
        }
    }

    #[must_use]
    pub fn pop(&mut self, id: Id<C>) -> Option<C> {
        let index_as_usize = id.index.into_usize().expect("invalid ComponentIndex");
        if self.items.len() <= index_as_usize { return None; }
        match replace(&mut self.items[index_as_usize], Left(self.vacancy)) {
            Left(vacancy) => {
                self.items[index_as_usize] = Left(vacancy);
                None
            },
            Right((unique, component)) => {
                if unique == id.unique {
                    self.vacancy = Some(id.index);
                    Some(component)
                } else {
                    self.items[index_as_usize] = Right((unique, component));
                    None
                }
            }
        }
    }

    pub fn get(&self, id: Id<C>) -> Option<&C> {
        let index_as_usize = id.index.into_usize().expect("invalid ComponentIndex");
        if self.items.len() <= index_as_usize { return None; }
        self.items[index_as_usize].as_ref().right().and_then(|&(unique, ref component)| {
            if unique == id.unique {
                Some(component)
            } else {
                None
            }
        })
    }

    pub fn get_mut(&mut self, id: Id<C>) -> Option<&mut C> {
        let index_as_usize = id.index.into_usize().expect("invalid ComponentIndex");
        if self.items.len() <= index_as_usize { return None; }
        self.items[index_as_usize].as_mut().right().and_then(|&mut (unique, ref mut component)| {
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

impl<C: Component> Index<Id<C>> for Arena<C> {
    type Output = C;

    fn index(&self, id: Id<C>) -> &C { self.get(id).expect("component not found") }
}

impl<C: Component> IndexMut<Id<C>> for Arena<C> {
    fn index_mut(&mut self, id: Id<C>) -> &mut C { self.get_mut(id).expect("component not found") }
}

/// Helps to store `ComponentClassToken` in a static.
#[cfg(feature="std")]
pub struct ComponentClassMutex<C: ComponentClass>(sync::Lazy<Mutex<ComponentClassToken<C>>>);

#[cfg(feature="std")]
impl<C: ComponentClass> ComponentClassMutex<C> {
    pub const fn new() -> Self {
        ComponentClassMutex(sync::Lazy::new(|| Mutex::new(
            ComponentClassToken::new().expect("component class token alread taken")
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
/// use std::num::NonZeroU64;
/// use components_arena::{ComponentClassMutex, Arena};
///
/// macro_attr! {
///     #[derive(Component!(index=u32, unique=NonZeroU64))]
///     struct Item { /* ... */ }
/// }
///
/// static ITEM: ComponentClassMutex<Item> = ComponentClassMutex::new();
///
/// // ...
///
/// fn main() {
///     let mut arena = Arena::new();
///     let id = arena.push(&mut ITEM.lock().unwrap(), |_| Item { /* ... */ });
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
/// use std::num::NonZeroU64;
/// use components_arena::{ComponentClassMutex, Arena};
///
/// macro_attr! {
///     #[derive(Component!(index=u32, unique=NonZeroU64, class=ItemComponent))]
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
///     let mut arena_u8 = Arena::new();
///     let _ = arena_u8.push(&mut ITEM.lock().unwrap(), |_| Item { context: 7u8 });
///
///     let mut arena_u32 = Arena::new();
///     let _ = arena_u32.push(&mut ITEM.lock().unwrap(), |_| Item { context: 7u32 });
/// }
/// ```
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
        impl $crate::ComponentClass for $name {
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
        impl $crate::ComponentClass for $class {
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
