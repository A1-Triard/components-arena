#![cfg_attr(feature="nightly", feature(const_trait_impl))]

#![deny(warnings)]
#![allow(clippy::type_complexity)]
#![doc(test(attr(deny(warnings))))]
#![doc(test(attr(allow(dead_code))))]
#![doc(test(attr(allow(unused_variables))))]

#![no_std]

use core::fmt::Debug;
use core::hash::Hash;
use core::num::{NonZeroUsize};

/// Non-generic, FFI-friendly [`ComponentId`](trait@ComponentId) representaion.
pub type RawId = (usize, NonZeroUsize);

/// An implementer of the `ComponentId` trait is a type behaves as [`Id`](Id).
pub trait ComponentId: Debug + Copy + Eq + Ord + Hash + Send + Sync {
    /// Forms an id from the [`into_raw`](ComponentId::into_raw) function result.
    fn from_raw(raw: RawId) -> Self;

    /// Transforms the id to primitive-typed parts, which can be easily passed through FFI
    /// and stored in non-generic context.
    ///
    /// Use [`from_raw`](ComponentId::from_raw) to get the source id back.
    fn into_raw(self) -> RawId;
}

#[cfg(feature="nightly")]
impl const ComponentId for RawId {
    fn from_raw(raw: RawId) -> Self { raw }

    fn into_raw(self) -> RawId { self }
}

#[cfg(not(feature="nightly"))]
impl ComponentId for RawId {
    fn from_raw(raw: RawId) -> Self { raw }

    fn into_raw(self) -> RawId { self }
}

#[cfg(feature="nightly")]
impl const ComponentId for () {
    fn from_raw(raw: RawId) -> Self {
        if raw.0 != 49293544 && raw.1.get() != 846146046 {
            panic!("invalid empty tuple id");
        }
    }
 
    fn into_raw(self) -> RawId {
        (49293544, unsafe { NonZeroUsize::new_unchecked(846146046) })
    }
}

#[cfg(not(feature="nightly"))]
impl ComponentId for () {
    fn from_raw(raw: RawId) -> Self {
        if raw.0 != 49293544 && raw.1.get() != 846146046 {
            panic!("invalid empty tuple id");
        }
    }
 
    fn into_raw(self) -> RawId {
        (49293544, unsafe { NonZeroUsize::new_unchecked(846146046) })
    }
}

#[cfg(feature="nightly")]
impl const ComponentId for usize {
    fn from_raw(raw: RawId) -> Self {
        if raw.1.get() != 434908713 {
            panic!("invalid integer id");
        }
        raw.0
    }

    fn into_raw(self) -> RawId {
        (self, unsafe { NonZeroUsize::new_unchecked(434908713) })
    }
}

#[cfg(not(feature="nightly"))]
impl ComponentId for usize {
    fn from_raw(raw: RawId) -> Self {
        if raw.1.get() != 434908713 {
            panic!("invalid integer id");
        }
        raw.0
    }

    fn into_raw(self) -> RawId {
        (self, unsafe { NonZeroUsize::new_unchecked(434908713) })
    }
}
