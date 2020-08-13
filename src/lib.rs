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
/// can used as a component actual id.
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
/// can be used as an index part of a component `Id`.
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

/// The return type of the `ComponentImpl::components_token_lock` function.
/// This structure is essential for components arena internal mechanic.
pub struct ComponentsTokenLock(AtomicBool);

impl ComponentsTokenLock {
    /// Creates new `ComponentsTokenLock` instance. The function is `const`,
    /// and can be used for static initialization.
    pub const fn new() -> Self { ComponentsTokenLock(AtomicBool::new(false)) }
}

impl Default for ComponentsTokenLock {
    fn default() -> Self { ComponentsTokenLock::new() }
}

/// Any type implementing this trait describes some class of components sharing
/// common `Id` generator,
/// so all components with same class are guaranteed to have distinct `Id`s.
///
/// Normaly for a non-generic component type
/// the component type itself implements `ComponentImpl`.
///
/// For generic components it would be difficult to have
/// an own `ComponentsTokenLock` instance for every specialization because Rust
/// does not have "generic statics" feature.
///
/// So, if some component type `X` is generic, normally you should introduce
/// common non-generic synthetic zero-sized type `XComponent` and implement
/// `ComponentImpl` for this synthetic type.
///
/// # Safety
///
/// Correct safe implementation should return reference to the one and same
/// `ComponentsTokenLock` instance from the `components_token_lock` function.
///
/// Also it should be garanteed that no other `ComponentImpl` implementation
/// returns same `ComponentsTokenLock` instance.
///
/// This requirements can be easaly satisfied with private static:
///
/// ```rust
/// static MY_COMPONENT_TOKEN_LOCK: ComponentsTokenLock = ComponentTokenLock::new();
/// unsafe impl ComponentImpl for MyComponent {
///     fn components_token_lock() -> &'static ComponentsTokenLock {
///         &MY_COMPONENT_TOKEN_LOCK
///     }
///     // ...
/// }
/// ```
pub unsafe trait ComponentImpl {
    /// First part of compound component id, distinct for all alive components.
    type Index: ComponentIndex;

    /// Second part of compound component id, distinct for all components
    /// created during application run time.
    type Id: ComponentId;

    /// Essential for components arena internal mechanic.
    fn components_token_lock() -> &'static ComponentsTokenLock;
}

/// Describes type, whose values can be put into arena container and accessed
/// through shared `Id`.
pub trait Component {
    /// Component class. Normally it is `Self` for non-generic types, and
    /// non-generic synthetic zero-sized type for generic ones.
    type Impl: ComponentImpl;

    /// Function returning `Self::Impl` type.
    /// This function is guaranteed to be never called, and may have any body.
    ///
    /// # Safety
    ///
    /// This function should not be called at all.
    /// There are no circumstances when such call could be safe.
    unsafe fn impl_type(self) -> Self::Impl;
}

/// Component handle. Distinct components are guaranteed to have distinct handles.
#[derive(Derivative)]
#[derivative(Debug(bound=""), Copy(bound=""), Clone(bound=""), Eq(bound=""), PartialEq(bound=""))]
#[derivative(Hash(bound=""), Ord(bound=""), PartialOrd(bound=""))]
pub struct Id<C: Component> {
    index: <<C as Component>::Impl as ComponentImpl>::Index,
    id: <<C as Component>::Impl as ComponentImpl>::Id,
}

/// The `Components` structure allows inserting and removing elements that are referred to by `Id`.
#[derive(Debug)]
pub struct Components<C: Component> {
    items: Vec<Option<(<<C as Component>::Impl as ComponentImpl>::Id, C)>>,
    vacancies: Vec<<<C as Component>::Impl as ComponentImpl>::Index>,
}

pub struct ComponentsToken<C: ComponentImpl>(Option<C::Id>);

impl<C: ComponentImpl> ComponentsToken<C> {
    pub fn new() -> Option<ComponentsToken<C>> {
        let lock = C::components_token_lock();
        if lock.0.compare_and_swap(false, true, Ordering::Relaxed) {
            None
        } else {
            Some(ComponentsToken(None))
        }
    }
}

impl<C: Component> Components<C> {
    pub fn new() -> Self {
        Components { items: Vec::new(), vacancies: Vec::new() }
    }

    pub fn attach(&mut self, token: &mut ComponentsToken<C::Impl>, component: impl FnOnce(Id<C>) -> C) -> Id<C> {
        let id = <<C as Component>::Impl as ComponentImpl>::Id::inc(token.0).expect("component ids exhausted");
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
    pub fn detach(&mut self, id: Id<C>) -> Option<C> {
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

impl<C: Component> Default for Components<C> {
    fn default() -> Self { Components::new() }
}

#[cfg(feature="std")]
pub struct ComponentsTokenMutex<C: ComponentImpl>(sync::Lazy<Mutex<ComponentsToken<C>>>);

#[cfg(feature="std")]
impl<C: ComponentImpl> ComponentsTokenMutex<C> {
    pub const fn new() -> Self {
        ComponentsTokenMutex(sync::Lazy::new(|| Mutex::new(
            ComponentsToken::new().unwrap_or_else(|| unsafe { unreachable_unchecked() })
        )))
    }
}

#[cfg(feature="std")]
impl<C: ComponentImpl> Deref for ComponentsTokenMutex<C> {
    type Target = Mutex<ComponentsToken<C>>;

    fn deref(&self) -> &Self::Target { self.0.deref() }
}

#[cfg(feature="std")]
#[macro_export]
macro_rules! Component {
    ((id=$id:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, id=$id) $($y)* }
    };
    ((impl=$impl:ident, $($x:tt),*) $($y:tt)*) => {
        Component! { ($($x)*, impl=$impl) $($y)* }
    };
    ((token=$token:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, token=$token) $($y)* }
    };
    ((index=$index:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, index=$index) $($y)* }
    };
    ((token_lock=$token_lock:ident, id=$id:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { (token_lock=$token_lock, $($x)*, id=$id) $($y)* }
    };
    ((token_lock=$token_lock:ident, impl=$impl:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (token_lock=$token_lock, $($x)*, impl=$impl) $($y)* }
    };
    ((token_lock=$token_lock:ident, token=$token:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (token_lock=$token_lock, $($x)*, token=$token) $($y)* }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, token=$token:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (token_lock=$token_lock, index=$index, $($x)*, token=$token) $($y)* }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, impl=$impl:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (token_lock=$token_lock, index=$index, $($x)*, impl=$impl) $($y)* }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, id=$id:ty, impl=$impl:ident, token=$token:ident) $($y:tt)*) => {
        Component! { ( token_lock=$token_lock, index=$index, id=$id, token=$token, impl=$impl ) $($y)* }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, id=$id:ty, token=$token:ident, impl=$impl:ident)
        $(pub $((crate))?)? struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock, $token, $impl,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, id=$id:ty, impl=$impl:ident)
        $(pub $((crate))?)? struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock, $impl,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, id=$id:ty, token=$token:ident)
        $(pub $((crate))?)? struct $name:ident
        { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock, $token
        }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, id=$id:ty)
        $(pub $((crate))?)? struct $name:ident
        { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock
        }
    };
    (@impl $name:ident, $id:ty, $index:ty, $token_lock:ident) => {
        static $token_lock: $crate::ComponentsTokenLock = $crate::ComponentsTokenLock::new();
        unsafe impl $crate::ComponentImpl for $name {
            type Id = $id;
            type Index = $index;
            fn components_token_lock() -> &'static $crate::ComponentsTokenLock { &$token_lock }
        }
        impl $crate::Component for $name {
            type Impl = Self;
            unsafe fn impl_type(self) -> Self { self }
        }
    };
    (@impl $name:ident, $id:ty, $index:ty, $token_lock:ident, $impl:ident, < $g:tt >, < $r:tt >) => {
        static $token_lock: $crate::ComponentsTokenLock = $crate::ComponentsTokenLock::new();
        struct $impl;
        unsafe impl $crate::ComponentImpl for $impl {
            type Id = $id;
            type Index = $index;
            fn components_token_lock() -> &'static $crate::ComponentsTokenLock { &$token_lock }
        }
        impl< $g > $crate::Component for $name < $r > {
            type Impl = impl $crate::ComponentImpl<id=$id, index=$index>;
            unsafe fn impl_type(self) -> Self::Impl { $impl }
        }
    };
    (@impl $name:ident, $id:ty, $index:ty, $token_lock:ident, $token:ident) => {
        static $token_lock: $crate::ComponentsTokenLock = $crate::ComponentsTokenLock::new();
        static $token: $crate::ComponentsTokenMutex<$name> = $crate::ComponentsTokenMutex::new();
        unsafe impl $crate::ComponentImpl for $name {
            type Id = $id;
            type Index = $index;
            fn components_token_lock() -> &'static $crate::ComponentsTokenLock { &$token_lock }
        }
        impl $crate::Component for $name {
            type Impl = Self;
            unsafe fn impl_type(self) -> Self { self }
        }
    };
    (@impl $name:ident, $id:ty, $index:ty, $token_lock:ident, $token:ident, $impl:ident, < $g:tt >, < $r:tt >) => {
        static $token_lock: $crate::ComponentsTokenLock = $crate::ComponentsTokenLock::new();
        static $token: $crate::ComponentsTokenMutex<$impl> = $crate::ComponentsTokenMutex::new();
        struct $impl;
        unsafe impl $crate::ComponentImpl for $impl {
            type Id = $id;
            type Index = $index;
            fn components_token_lock() -> &'static $crate::ComponentsTokenLock { &$token_lock }
        }
        impl< $g > $crate::Component for $name < $r > {
            type Impl = impl $crate::ComponentImpl<id=$id, index=$index>;
            unsafe fn impl_type(self) -> Self::Impl { $impl }
        }
    };
}

#[cfg(not(feature="std"))]
#[macro_export]
macro_rules! Component {
    ((id=$id:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, id=$id) $($y)* }
    };
    ((impl=$impl:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, impl=$impl) $($y)* }
    };
    ((index=$index:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, index=$index) $($y)* }
    };
    ((token_lock=$token_lock:ident, id=$id:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { (token_lock=$token_lock, $($x)*, id=$id) $($y)* }
    };
    ((token_lock=$token_lock:ident, impl=$impl:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (token_lock=$token_lock, $($x)*, impl=$impl) $($y)* }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, impl=$impl:ident, id=$id:ty) $($y:tt)*) => {
        Component! { (token_lock=$token_lock, index=$index, id=$id, impl=$impl) $($y)* }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, id=$id:ty, impl=$impl:ident)
        $(pub $((crate))?)? struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock, $impl,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((token_lock=$token_lock:ident, index=$index:ty, id=$id:ty)
        $(pub $((crate))?)? struct $name:ident
        { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock
        }
    };
    (@impl $name:ident, $id:ty, $index:ty, $token_lock:ident) => {
        static $token_lock: $crate::ComponentsTokenLock = $crate::ComponentsTokenLock::new();
        unsafe impl $crate::ComponentImpl for $name {
            type Id = $id;
            type Index = $index;
            fn components_token_lock() -> &'static $crate::ComponentsTokenLock { &$token_lock }
        }
        impl $crate::Component for $name {
            type Impl = Self;
            unsafe fn impl_type(self) -> Self { self }
        }
    };
    (@impl $name:ident, $id:ty, $index:ty, $token_lock:ident, $impl:ident, < $g:tt >, < $r:tt >) => {
        static $token_lock: $crate::ComponentsTokenLock = $crate::ComponentsTokenLock::new();
        struct $impl;
        unsafe impl $crate::ComponentImpl for $impl {
            type Id = $id;
            type Index = $index;
            fn components_token_lock() -> &'static $crate::ComponentsTokenLock { &$token_lock }
        }
        impl< $g > $crate::Component for $name < $r > {
            type Impl = impl $crate::ComponentImpl<id=$id, index=$index>;
            unsafe fn impl_type(self) -> Self::Impl { $impl }
        }
    };
}
