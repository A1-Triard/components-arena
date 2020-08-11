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
use std::ops::Deref;
use std::sync::atomic::{AtomicBool, Ordering};
use std::vec::Vec;
#[cfg(feature="std")]
use once_cell::sync::{self};
#[cfg(feature="std")]
use std::sync::Mutex;

pub unsafe trait ComponentId: Debug + Copy + Eq + Hash + Ord {
    fn inc(this: Option<Self>) -> Option<Self>;
}

unsafe impl ComponentId for NonZeroU8 {
    fn inc(this: Option<Self>) -> Option<Self> { Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0) }
}

unsafe impl ComponentId for NonZeroU16 {
    fn inc(this: Option<Self>) -> Option<Self> { Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0) }
}

unsafe impl ComponentId for NonZeroU32 {
    fn inc(this: Option<Self>) -> Option<Self> { Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0) }
}

unsafe impl ComponentId for NonZeroU64 {
    fn inc(this: Option<Self>) -> Option<Self> { Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0) }
}

unsafe impl ComponentId for NonZeroU128 {
    fn inc(this: Option<Self>) -> Option<Self> { Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0) }
}

unsafe impl ComponentId for NonZeroUsize {
    fn inc(this: Option<Self>) -> Option<Self> { Self::new(this.map_or(0, |x| x.get()).overflowing_add(1).0) }
}

pub unsafe trait ComponentIndex: Debug + Copy + Eq + Hash + Ord + TryInto<usize> + TryFrom<usize> { }

unsafe impl ComponentIndex for u8 { }

unsafe impl ComponentIndex for u16 { }

unsafe impl ComponentIndex for u32 { }

unsafe impl ComponentIndex for u64 { }

unsafe impl ComponentIndex for u128 { }

unsafe impl ComponentIndex for usize { }

pub struct ComponentsTokenLock(AtomicBool);

impl ComponentsTokenLock {
    pub const fn new() -> Self { ComponentsTokenLock(AtomicBool::new(false)) }
}

impl Default for ComponentsTokenLock {
    fn default() -> Self { ComponentsTokenLock::new() }
}

pub unsafe trait ComponentImpl {
    type Id: ComponentId;
    type Index: ComponentIndex;
    fn components_token_lock() -> &'static ComponentsTokenLock;
}

pub unsafe trait Component {
    type Impl: ComponentImpl;
    unsafe fn impl_type(self) -> Self::Impl;
}

#[derive(Derivative)]
#[derivative(Debug(bound=""), Copy(bound=""), Clone(bound=""), Eq(bound=""), PartialEq(bound=""))]
#[derivative(Hash(bound=""), Ord(bound=""), PartialOrd(bound=""))]
pub struct Id<C: Component> {
    index: <<C as Component>::Impl as ComponentImpl>::Index,
    id: <<C as Component>::Impl as ComponentImpl>::Id,
}

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
            ComponentsToken::new().unwrap_or_else(|| unsafe { ::std::hint::unreachable_unchecked() })
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
    ((Id=$id:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, Id=$id) $($y)* }
    };
    ((Impl=$impl:ident, $($x:tt),*) $($y:tt)*) => {
        Component! { ($($x)*, Impl=$impl) $($y)* }
    };
    ((TOKEN=$token:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, TOKEN=$token) $($y)* }
    };
    ((Index=$index:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, Index=$index) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Id=$id:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { (TOKEN_LOCK=$token_lock, $($x)*, Id=$id) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Impl=$impl:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (TOKEN_LOCK=$token_lock, $($x)*, Impl=$impl) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, TOKEN=$token:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (TOKEN_LOCK=$token_lock, $($x)*, TOKEN=$token) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, TOKEN=$token:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (TOKEN_LOCK=$token_lock, Index=$index, $($x)*, TOKEN=$token) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Impl=$impl:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (TOKEN_LOCK=$token_lock, Index=$index, $($x)*, Impl=$impl) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Id=$id:ty, Impl=$impl:ident, TOKEN=$token:ident) $($y:tt)*) => {
        Component! { ( TOKEN_LOCK=$token_lock, Index=$index, Id=$id, TOKEN=$token, Impl=$impl ) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Id=$id:ty, TOKEN=$token:ident, Impl=$impl:ident)
        $(pub $((crate))?)? struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock, $token, $impl,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Id=$id:ty, Impl=$impl:ident)
        $(pub $((crate))?)? struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock, $impl,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Id=$id:ty, TOKEN=$token:ident)
        $(pub $((crate))?)? struct $name:ident
        { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock, $token
        }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Id=$id:ty)
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
        unsafe impl $crate::Component for $name {
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
        unsafe impl< $g > $crate::Component for $name < $r > {
            type Impl = impl $crate::ComponentImpl<Id=$id, Index=$index>;
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
        unsafe impl $crate::Component for $name {
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
        unsafe impl< $g > $crate::Component for $name < $r > {
            type Impl = impl $crate::ComponentImpl<Id=$id, Index=$index>;
            unsafe fn impl_type(self) -> Self::Impl { $impl }
        }
    };
}

#[cfg(not(feature="std"))]
#[macro_export]
macro_rules! Component {
    ((Id=$id:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, Id=$id) $($y)* }
    };
    ((Impl=$impl:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, Impl=$impl) $($y)* }
    };
    ((Index=$index:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { ($($x)*, Index=$index) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Id=$id:ty, $($x:tt)*) $($y:tt)*) => {
        Component! { (TOKEN_LOCK=$token_lock, $($x)*, Id=$id) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Impl=$impl:ident, $($x:tt)*) $($y:tt)*) => {
        Component! { (TOKEN_LOCK=$token_lock, $($x)*, Impl=$impl) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Impl=$impl:ident, Id=$id:ty) $($y:tt)*) => {
        Component! { (TOKEN_LOCK=$token_lock, Index=$index, Id=$id, Impl=$impl) $($y)* }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Id=$id:ty, Impl=$impl:ident)
        $(pub $((crate))?)? struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > { $($tail:tt)* } ) => {
        Component! {
            @impl $name, $id, $index, $token_lock, $impl,
            < $( $lt ),+ >,
            < $( $lt $( : $clt $(+ $dlt )* )? ),+ >
        }
    };
    ((TOKEN_LOCK=$token_lock:ident, Index=$index:ty, Id=$id:ty)
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
        unsafe impl $crate::Component for $name {
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
        unsafe impl< $g > $crate::Component for $name < $r > {
            type Impl = impl $crate::ComponentImpl<Id=$id, Index=$index>;
            unsafe fn impl_type(self) -> Self::Impl { $impl }
        }
    };
}
