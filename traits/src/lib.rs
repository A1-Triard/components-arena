#![cfg_attr(feature="nightly", feature(const_trait_impl))]
#![cfg_attr(feature="nightly", feature(effects))]

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

/// An implementer of the `ComponentId` trait is a type behaves as
/// [`Id`](https://docs.rs/components-arena/latest/components_arena/struct.Id.html).
#[cfg_attr(feature="nightly", const_trait)]
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
include!("nightly.rs");

#[cfg(not(feature="nightly"))]
include!("stable.rs");
