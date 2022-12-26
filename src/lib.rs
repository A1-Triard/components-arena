#![cfg_attr(feature="nightly", feature(allocator_api))]
#![cfg_attr(feature="nightly", feature(associated_type_defaults))]
#![cfg_attr(feature="nightly", feature(const_trait_impl))]

#![deny(warnings)]
#![doc(test(attr(deny(warnings))))]
#![doc(test(attr(allow(dead_code))))]
#![doc(test(attr(allow(unused_variables))))]
#![allow(clippy::type_complexity)]

//! ## Feature flags
#![doc=document_features::document_features!()]

#![no_std]

#[doc=include_str!("../README.md")]
type _DocTestReadme = ();

extern crate alloc as alloc_crate;

#[doc(hidden)]
pub use core::compile_error as std_compile_error;
#[doc(hidden)]
pub use core::concat as std_concat;
#[doc(hidden)]
pub use core::default::Default as std_default_Default;
#[doc(hidden)]
pub use core::option::Option as std_option_Option;
#[doc(hidden)]
pub use core::stringify as std_stringify;
#[doc(hidden)]
pub use generics::parse as generics_parse;

#[cfg(feature="nightly")]
use alloc_crate::alloc::Allocator;
use alloc_crate::collections::TryReserveError;
use alloc_crate::vec::{self, Vec};
#[cfg(feature="nightly")]
use composable_allocators::Global as Global;
use core::fmt::Debug;
use core::hint::unreachable_unchecked;
use core::iter::{self, FusedIterator};
use core::mem::{align_of, replace, size_of};
use core::num::NonZeroUsize;
use core::ops::{Index, IndexMut};
use core::slice::{self};
use core::sync::atomic::{AtomicUsize, Ordering};
use educe::Educe;
use either::{Either, Left, Right};
use phantom_type::PhantomType;
use rand::rngs::SmallRng;
use rand::{RngCore, SeedableRng};

pub use components_arena_traits::*;

/// [Component class](ComponentClass) static shared data.
/// The return type of the [`ComponentClass::token`](ComponentClass::token) function.
///
/// The [`ComponentClass::token`](ComponentClass::token) function
/// is essential for components arena internal mechanic.
pub struct ComponentClassToken(AtomicUsize);

impl ComponentClassToken {
    /// Creates new `ComponentClassLock` instance.
    ///
    /// The function is `const`, and can be used for static initialization.
    pub const fn new() -> Self { ComponentClassToken(AtomicUsize::new(0)) }
}

impl Default for ComponentClassToken {
    fn default() -> Self { ComponentClassToken::new() }
}

/// An utility trait describing a specific component type.
///
/// Normally for a non-generic component type
/// the component type itself implements `ComponentClass`.
///
/// For generic components it would be difficult to have
/// an own [`ComponentClassToken`](ComponentClassToken) instance for every specialization because Rust
/// does not have "generic statics" feature.
///
/// So, if some component type `X` is generic, normally you should introduce
/// common non-generic uninhabited type `XComponent` and implement
/// `ComponentClass` for this synthetic type.
///
/// Correct implementation should return reference to the one and same
/// `ComponentClassToken` instance from the [`token`](ComponentClass::token) function.
/// Also it should be guaranteed that no other `ComponentClass` implementation
/// returns same `ComponentClassLock` instance.
/// This requirements can be easily satisfied with private static:
///
/// ```rust
/// # use components_arena::{ComponentClass, ComponentClassToken};
/// #
/// struct MyComponent { /* ... */ }
///
/// impl ComponentClass for MyComponent {
///     fn token() -> &'static ComponentClassToken {
///         static TOKEN: ComponentClassToken = ComponentClassToken::new();
///         &TOKEN
///     }
/// }
/// ```
pub trait ComponentClass {
    /// Essential for components arena internal mechanic.
    fn token() -> &'static ComponentClassToken where Self: Sized;
}

/// An implementer of the `Component` trait is a type, whose values can be placed into
/// [`Arena`](Arena) container.
///
/// Normally, the implementation of this trait is derived
/// using the [`Component!`](Component!) macro.
pub trait Component {
    /// Component class.
    ///
    /// Normally it is `Self` for non-generic types, and
    /// non-generic synthetic uninhabited type for generic ones.
    type Class: ComponentClass;

    /// Component allocator.
    ///
    /// [`Arena`]`<Self>` will use this allocator to allocate memory
    /// for components array.
    #[cfg(feature="nightly")]
    type Alloc: Allocator = Global;
}

/// [`Arena`](Arena) item handle.
#[derive(Educe)]
#[educe(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Id<C: Component> {
    index: usize,
    guard: NonZeroUsize,
    phantom: PhantomType<C>
}

#[cfg(feature="nightly")]
include!("impl_id_nightly.rs");

#[cfg(not(feature="nightly"))]
include!("impl_id_stable.rs");

type ArenaItem<C> = Either<Option<usize>, (NonZeroUsize, C)>;

/// A (mostly read-only) inner container holding [`Arena`](Arena) items.
/// While [`Arena`](Arena) itself is unique (i.e. non-clonable) object,
/// arena ['items'](Arena::items) could be cloned.
#[derive(Debug, Clone)]
pub struct ArenaItems<C: Component> {
    #[cfg(feature="nightly")]
    vec: Vec<ArenaItem<C>, C::Alloc>,

    #[cfg(not(feature="nightly"))]
    vec: Vec<ArenaItem<C>>,

    vacancy: Option<usize>,
}

impl<C: Component> ArenaItems<C> {
    /// An amount of memory required to hold one component.
    ///
    /// This information can be useful for memory management fine-tuning.
    pub const fn item_size() -> usize {
        size_of::<ArenaItem<C>>()
    }

    /// An alignment of a cell, holding a component with all required metadata.
    ///
    /// This information can be useful for memory management fine-tuning.
    pub const fn item_align() -> usize {
        align_of::<ArenaItem<C>>()
    }

    #[cfg(feature="nightly")]
    const fn new_in(alloc: C::Alloc) -> Self {
        ArenaItems {
            vec: Vec::new_in(alloc),
            vacancy: None
        }
    }

    #[cfg(not(feature="nightly"))]
    const fn new() -> Self {
        ArenaItems {
            vec: Vec::new(),
            vacancy: None
        }
    }

    #[cfg(feature="nightly")]
    fn with_capacity_in(capacity: usize, alloc: C::Alloc) -> Self {
        ArenaItems {
            vec: Vec::with_capacity_in(capacity, alloc),
            vacancy: None
        }
    }

    #[cfg(not(feature="nightly"))]
    fn with_capacity(capacity: usize) -> Self {
        ArenaItems {
            vec: Vec::with_capacity(capacity),
            vacancy: None
        }
    }

    /// Returns a reference to the underlying allocator.
    #[cfg(feature="nightly")]
    pub fn allocator(&self) -> &C::Alloc { self.vec.allocator() }

    /// Returns the number of elements the arena can hold without reallocating.
    pub fn capacity(&self) -> usize { self.vec.capacity() }

    /// Returns the number of elements in the arena.
    ///
    /// This function has linear worst-case complexity.
    pub fn len(&self) -> usize {
        let mut vacancies = 0;
        let mut vacancy = self.vacancy;
        while let Some(i) = vacancy {
            vacancies += 1;
            vacancy = *self.vec[i].as_ref().left().unwrap();
        }
        self.vec.len() - vacancies
    }

    /// Returns `true` if the arena contains no elements.
    ///
    /// This function has linear worst-case complexity.
    pub fn is_empty(&self) -> bool { self.vec.iter().all(|x| x.is_left()) }

    /// Returns the maximum number of elements ever in the arena.
    /// The arena capacity cannot be less than `min_capacity`.
    ///
    /// Arena `min_capacity` never decreases.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use macro_attr_2018::macro_attr;
    /// # use components_arena::{Component, Arena};
    /// #
    /// # macro_attr! {
    /// #     #[derive(Component!)]
    /// #     struct MyComponent { /* ... */ }
    /// # }
    /// #
    /// # fn main() {
    /// let mut arena = Arena::new();
    /// assert_eq!(arena.items().min_capacity(), 0);
    /// let id_1 = arena.insert(|id| (MyComponent { /* ... */ }, id));
    /// assert_eq!(arena.items().min_capacity(), 1);
    /// let id_2 = arena.insert(|id| (MyComponent { /* ... */ }, id));
    /// assert_eq!(arena.items().min_capacity(), 2);
    /// arena.remove(id_1);
    /// assert_eq!(arena.items().min_capacity(), 2);
    /// let id_3 = arena.insert(|id| (MyComponent { /* ... */ }, id));
    /// assert_eq!(arena.items().min_capacity(), 2);
    /// let id_4 = arena.insert(|id| (MyComponent { /* ... */ }, id));
    /// assert_eq!(arena.items().min_capacity(), 3);
    /// # }
    /// ```
    pub fn min_capacity(&self) -> usize { self.vec.len() }

    /// Reserves capacity for at least `additional` more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `reserve`, capacity will be greater than or equal to
    /// `self.min_capacity() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    pub fn reserve(&mut self, additional: usize) { self.vec.reserve(additional) }

    /// Reserves the minimum capacity for exactly `additional` more elements.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.min_capacity() + additional`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore, capacity can not be relied upon to be precisely minimal.
    /// Prefer [`reserve`](ArenaItems::reserve) if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    pub fn reserve_exact(&mut self, additional: usize) { self.vec.reserve_exact(additional) }

    /// Shrinks the capacity of the arena with a lower bound.
    ///
    /// The capacity will remain at least as large as both the [`min_capacity`](ArenaItems::min_capacity)
    /// and the supplied value.
    pub fn shrink_to(&mut self, min_capacity: usize) { self.vec.shrink_to(min_capacity) }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the [`min_capacity`](ArenaItems::min_capacity)
    /// but the allocator may still inform the arena that there is space for a few more elements.
    pub fn shrink_to_fit(&mut self) { self.vec.shrink_to_fit() }

    /// Tries to reserve capacity for at least additional more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `try_reserve`, capacity will be greater than or equal
    /// to `self.min_capacity() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve(additional)
    }

    /// Tries to reserve capacity for exactly `additional` more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or equal
    /// to `self.min_capacity() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore, capacity can not be relied upon to be precisely minimal.
    /// Prefer [`try_reserve`](ArenaItems::try_reserve) if future insertions are expected.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve_exact(additional)
    }

    /// Returns item occupying `index` place with its [`Id`](Id), or `None` if there is no such.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than or equal to [`min_capacity()`](ArenaItems::min_capacity).
    pub fn get_id_value(&self, index: usize) -> Option<(Id<C>, &C)> {
        self.vec[index].as_ref().right().map(|(guard, item)| (Id { index, guard: *guard, phantom: PhantomType::new() }, item))
    }

    /// Returns [`Id`](Id) of item occupying `index` place, or `None` if there is no such.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than or equal to [`min_capacity()`](ArenaItems::min_capacity).
    pub fn get_id(&self, index: usize) -> Option<Id<C>> {
        self.vec[index].as_ref().right().map(|(guard, _)| Id { index, guard: *guard, phantom: PhantomType::new() })
    }

    /// Returns item occupying `index` place, or `None` if there is no such.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than or equal to [`min_capacity()`](ArenaItems::min_capacity).
    pub fn get_value(&self, index: usize) -> Option<&C> {
        self.vec[index].as_ref().right().map(|(_, item)| item)
    }

    /// Returns an iterator over all item ids.
    pub fn ids(&self) -> ArenaItemsIds<C> {
        ArenaItemsIds(self.vec.iter().enumerate())
    }

    /// Returns an iterator over all items.
    pub fn values(&self) -> ArenaItemsValues<C> {
        ArenaItemsValues(self.vec.iter())
    }

    /// Returns an iterator over all items combined with their ids.
    pub fn iter(&self) -> ArenaItemsIter<C> {
        ArenaItemsIter(self.vec.iter().enumerate())
    }

    /// Transforms the container into an iterator over all items ids.
    pub fn into_ids(self) -> ArenaItemsIntoIds<C> {
        ArenaItemsIntoIds(self.vec.into_iter().enumerate())
    }

    /// Transforms the container into an iterator over all items.
    pub fn into_values(self) -> ArenaItemsIntoValues<C> {
        ArenaItemsIntoValues(self.vec.into_iter())
    }
}

/// An iterator over all items combined with their ids.
///
/// Usually created by the [`ArenaItems::iter`](ArenaItems::iter) method.
#[derive(Debug, Clone)]
pub struct ArenaItemsIter<'a, C: Component>(
    iter::Enumerate<slice::Iter<'a, Either<Option<usize>, (NonZeroUsize, C)>>>
);

impl<'a, C: Component> Iterator for ArenaItemsIter<'a, C> {
    type Item = (Id<C>, &'a C);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right((guard, item)))) =>
                    return Some((Id { index, guard: *guard, phantom: PhantomType::new() }, item)),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<'a, C: Component> DoubleEndedIterator for ArenaItemsIter<'a, C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right((guard, item)))) =>
                    return Some((Id { index, guard: *guard, phantom: PhantomType::new() }, item)),
            }
        }
    }
}

impl<'a, C: Component> FusedIterator for ArenaItemsIter<'a, C> { }

/// An iterator over all items ids.
///
/// Usually created by the [`ArenaItems::ids`](ArenaItems::ids) method.
#[derive(Debug, Clone)]
pub struct ArenaItemsIds<'a, C: Component>(
    iter::Enumerate<slice::Iter<'a, Either<Option<usize>, (NonZeroUsize, C)>>>
);

impl<'a, C: Component> Iterator for ArenaItemsIds<'a, C> {
    type Item = Id<C>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right((guard, _)))) => return Some(Id { index, guard: *guard, phantom: PhantomType::new() }),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<'a, C: Component> DoubleEndedIterator for ArenaItemsIds<'a, C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right((guard, _)))) => return Some(Id { index, guard: *guard, phantom: PhantomType::new() }),
            }
        }
    }
}

impl<'a, C: Component> FusedIterator for ArenaItemsIds<'a, C> { }

/// An iterator over all items.
///
/// Usually created by the [`ArenaItems::values`](ArenaItems::values) method.
#[derive(Debug, Clone)]
pub struct ArenaItemsValues<'a, C: Component>(
    slice::Iter<'a, Either<Option<usize>, (NonZeroUsize, C)>>
);

impl<'a, C: Component> Iterator for ArenaItemsValues<'a, C> {
    type Item = &'a C;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right((_, item))) => return Some(item),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<'a, C: Component> DoubleEndedIterator for ArenaItemsValues<'a, C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right((_, item))) => return Some(item),
            }
        }
    }
}

impl<'a, C: Component> FusedIterator for ArenaItemsValues<'a, C> { }

/// An iterator over all items ids.
///
/// Usually created by the [`ArenaItems::into_ids`](ArenaItems::into_ids) method.
#[derive(Debug)]
pub struct ArenaItemsIntoIds<C: Component>(
    #[cfg(feature="nightly")]
    iter::Enumerate<vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>, C::Alloc>>,

    #[cfg(not(feature="nightly"))]
    iter::Enumerate<vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>>>,
);

impl<C: Component> Iterator for ArenaItemsIntoIds<C> {
    type Item = Id<C>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right((guard, _)))) => return Some(Id { index, guard, phantom: PhantomType::new() }),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<C: Component> DoubleEndedIterator for ArenaItemsIntoIds<C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right((guard, _)))) => return Some(Id { index, guard, phantom: PhantomType::new() }),
            }
        }
    }
}

impl<C: Component> FusedIterator for ArenaItemsIntoIds<C> { }

/// An iterator over all items.
///
/// Usually created by the [`ArenaItems::into_values`](ArenaItems::into_values) method.
#[derive(Debug)]
pub struct ArenaItemsIntoValues<C: Component>(
    #[cfg(feature="nightly")]
    vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>, C::Alloc>,

    #[cfg(not(feature="nightly"))]
    vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>>,
);

impl<C: Component> Iterator for ArenaItemsIntoValues<C> {
    type Item = C;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right((_, item))) => return Some(item),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<C: Component> DoubleEndedIterator for ArenaItemsIntoValues<C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right((_, item))) => return Some(item),
            }
        }
    }
}

impl<C: Component> FusedIterator for ArenaItemsIntoValues<C> { }

/// An iterator over all items combined with their ids.
///
/// Usually created by the [`ArenaItems::into_iter`](ArenaItems::into_iter) method.
#[derive(Debug, Clone)]
pub struct ArenaItemsIntoIter<C: Component>(
    #[cfg(feature="nightly")]
    iter::Enumerate<vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>, C::Alloc>>,

    #[cfg(not(feature="nightly"))]
    iter::Enumerate<vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>>>,
);

impl<C: Component> Iterator for ArenaItemsIntoIter<C> {
    type Item = (Id<C>, C);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right((guard, item)))) =>
                    return Some((Id { index, guard, phantom: PhantomType::new() }, item)),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<C: Component> DoubleEndedIterator for ArenaItemsIntoIter<C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right((guard, item)))) =>
                    return Some((Id { index, guard, phantom: PhantomType::new() }, item)),
            }
        }
    }
}

impl<C: Component> FusedIterator for ArenaItemsIntoIter<C> { }

impl<C: Component> IntoIterator for ArenaItems<C> {
    type Item = (Id<C>, C);
    type IntoIter = ArenaItemsIntoIter<C>;

    fn into_iter(self) -> Self::IntoIter {
        ArenaItemsIntoIter(self.vec.into_iter().enumerate())
    }
}

impl<'a, C: Component> IntoIterator for &'a ArenaItems<C> {
    type Item = (Id<C>, &'a C);
    type IntoIter = ArenaItemsIter<'a, C>;

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

mod forgettable_field {
    use core::fmt::{self, Debug, Formatter};
    use core::mem::{MaybeUninit, forget, replace};
    use core::ops::{Deref, DerefMut};

    pub struct ForgettableField<T>(MaybeUninit<T>);

    impl<T> ForgettableField<T> {
        pub const fn new(value: T) -> Self { ForgettableField(MaybeUninit::new(value)) }

        pub fn into_inner(mut this: Self) -> T {
            let inner = replace(&mut this.0, MaybeUninit::uninit());
            forget(this);
            unsafe { inner.assume_init() }
        }

        pub fn take_and_forget<Owner>(mut owner: Owner, f: impl FnOnce(&mut Owner) -> &mut Self) -> T {
            let this = replace(f(&mut owner), ForgettableField(MaybeUninit::uninit()));
            forget(owner);
            Self::into_inner(this)
        }
    }

    impl<T> Drop for ForgettableField<T> {
        fn drop(&mut self) {
            unsafe { self.0.assume_init_drop() }
        }
    }

    impl<T> Deref for ForgettableField<T> {
        type Target = T;

        fn deref(&self) -> &T { unsafe { self.0.assume_init_ref() } }
    }

    impl<T> DerefMut for ForgettableField<T> {
        fn deref_mut(&mut self) -> &mut T { unsafe { self.0.assume_init_mut() } }
    }

    impl<T: Default> Default for ForgettableField<T> {
        fn default() -> Self { ForgettableField::new(T::default()) }
    }

    impl<T: Debug> Debug for ForgettableField<T> {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            self.deref().fmt(f)
        }
    }
}

use forgettable_field::*;

/// Unordered container with random access.
#[cfg(feature="nightly")]
#[derive(Educe)]
#[educe(Debug(bound = "C: Debug, C::Alloc: Debug"))]
pub struct Arena<C: Component + 'static> {
    guard_rng: Option<SmallRng>,
    items: ForgettableField<ArenaItems<C>>,
}

/// Unordered container with random access.
#[cfg(not(feature="nightly"))]
#[derive(Debug)]
pub struct Arena<C: Component + 'static> {
    guard_rng: Option<SmallRng>,
    items: ForgettableField<ArenaItems<C>>,
}

#[cfg(feature="nightly")]
include!("arena_nightly.rs");

impl<C: Component> Arena<C> {
    /// Creates an arena instance.
    #[cfg(not(feature="nightly"))]
    pub const fn new() -> Self {
        Arena {
            guard_rng: None,
            items: ForgettableField::new(ArenaItems::new())
        }
    }

    /// Creates an arena instance with the specified initial capacity.
    #[cfg(not(feature="nightly"))]
    pub fn with_capacity(capacity: usize) -> Self {
        Arena {
            guard_rng: None,
            items: ForgettableField::new(ArenaItems::with_capacity(capacity))
        }
    }

    /// Creates an arena instance.
    #[cfg(feature="nightly")]
    pub const fn new_in(alloc: C::Alloc) -> Self {
        Arena {
            guard_rng: None,
            items: ForgettableField::new(ArenaItems::new_in(alloc))
        }
    }

    /// Creates an arena instance with the specified initial capacity.
    #[cfg(feature="nightly")]
    pub fn with_capacity_in(capacity: usize, alloc: C::Alloc) -> Self {
        Arena {
            guard_rng: None,
            items: ForgettableField::new(ArenaItems::with_capacity_in(capacity, alloc))
        }
    }

    fn guard_rng(&mut self) -> &mut SmallRng {
        if self.guard_rng.is_none() {
            let seed = C::Class::token().0.fetch_add(1, Ordering::Relaxed);
            self.guard_rng = Some(SmallRng::seed_from_u64(seed as u64));
        }
        unsafe { self.guard_rng.as_mut().unwrap_or_else(|| unreachable_unchecked()) }
    }

    /// Returns contained items packed in a special container.
    /// While arena itself is unique (i.e. non-clonable) object,
    /// this special container could be cloned.
    pub fn into_items(#[allow(unused_mut)] mut self) -> ArenaItems<C> {
        ForgettableField::take_and_forget(self, |x| &mut x.items)
    }

    /// Returns reference to contained items packed in a special container.
    /// While arena itself is unique (i.e. non-clonable) object,
    /// this special container could be cloned.
    pub fn items(&self) -> &ArenaItems<C> { &self.items }

    /// Returns mutable reference to contained items packed in
    /// a (mostly read-only) special container.
    /// While arena itself is unique (i.e. non-clonable) object,
    /// this special container could be cloned.
    pub fn items_mut(&mut self) -> &mut ArenaItems<C> { &mut self.items }

    /// Place new component into the arena.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use macro_attr_2018::macro_attr;
    /// # use components_arena::{Component, Arena};
    /// #
    /// # macro_attr! {
    /// #     #[derive(Component!)]
    /// #     struct MyComponent { /* ... */ }
    /// # }
    /// #
    /// # fn main() {
    /// let mut arena = Arena::new();
    /// let new_component_id = arena.insert(|id| (MyComponent { /* ... */ }, id));
    /// # }
    /// ```
    pub fn insert<T>(&mut self, component: impl FnOnce(Id<C>) -> (C, T)) -> T {
        let mut guard = 0usize.to_le_bytes();
        self.guard_rng().fill_bytes(&mut guard[..]);
        let guard = NonZeroUsize::new(usize::from_le_bytes(guard)).unwrap_or(unsafe { NonZeroUsize::new_unchecked(42) });
        if let Some(index) = self.items.vacancy {
            let id = Id { index, guard, phantom: PhantomType::new() };
            let (component, result) = component(id);
            let item = (guard, component);
            self.items.vacancy = replace(&mut self.items.vec[index], Right(item)).left()
                .unwrap_or_else(|| unsafe { unreachable_unchecked() });
            result
        } else {
            let index = self.items.len();
            let id = Id { index, guard, phantom: PhantomType::new() };
            let (component, result) = component(id);
            let item = (guard, component);
            self.items.vec.push(Right(item));
            result
        }
    }

    /// Removes component with provided id.
    ///
    /// The arena tries to detect invalid provided id (i.e. foreign, or previously dropped),
    /// and panics if such detection hits. But it is important to pay respect to the fact
    /// there is small probability that invalid id will not be intercepted.
    pub fn remove(&mut self, id: Id<C>) -> C {
        let vacancy = self.items.vacancy;
        match replace(&mut self.items.vec[id.index], Left(vacancy)) {
            Left(vacancy) => {
                self.items.vec[id.index] = Left(vacancy);
                panic!("invalid id");
            },
            Right((guard, component)) => {
                if guard == id.guard {
                    self.items.vacancy = Some(id.index);
                    component
                } else {
                    self.items.vec[id.index] = Right((guard, component));
                    panic!("invalid id");
                }
            }
        }
    }
}

#[cfg(feature="nightly")]
impl<C: Component> Default for Arena<C> where C::Alloc: Default {
    fn default() -> Self { Arena::new() }
}

#[cfg(not(feature="nightly"))]
impl<C: Component> Default for Arena<C> {
    fn default() -> Self { Arena::new() }
}

impl<C: Component> Index<Id<C>> for Arena<C> {
    type Output = C;

    fn index(&self, id: Id<C>) -> &C {
        let &(guard, ref component) = self.items.vec[id.index].as_ref().right().expect("invalid id");
        if guard != id.guard { panic!("invalid id"); }
        component
    }
}

impl<C: Component> IndexMut<Id<C>> for Arena<C> {
    fn index_mut(&mut self, id: Id<C>) -> &mut C {
        let &mut (guard, ref mut component) = self.items.vec[id.index].as_mut().right().expect("invalid id");
        if guard != id.guard { panic!("invalid id"); }
        component
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! unexpected_token {
    () => { };
}

/// [Macro attribute](https://crates.io/crates/macro-attr-2018) for deriving [`Component`](trait@Component) trait.
///
/// Accepts input in the following form:
///
/// ```ignore
/// ($($(
///     $param
/// ),+ $(,)?)?)
/// $vis:vis $(enum | struct) $name:ident
/// $(
///     <$generics>
///     $($tokens_between_generics_and_where_clause:tt)*
///     $(where $where_clause)?
/// )?
/// $( ; | { $($body:tt)* } )
/// ```
///
/// where $param may be in any of following forms:
///
/// ```ignore
/// class = $Class:ident
/// ```
///
/// ```ignore
/// alloc = $Allocator:ty
/// ```
///
/// # Examples
///
/// ## Non-generic component
///
/// ```rust
/// # use macro_attr_2018::macro_attr;
/// # use components_arena::{Component, Arena};
/// #
/// macro_attr! {
///     #[derive(Component!)]
///     struct Item { /* ... */ }
/// }
///
/// // ...
///
/// # fn main() {
/// let mut arena = Arena::new();
/// let id = arena.insert(|id| (Item { /* ... */ }, id));
/// # }
/// ```
///
/// ## Generic component
///
/// ```rust
/// # use macro_attr_2018::macro_attr;
/// # use components_arena::{Component, Arena};
/// #
/// macro_attr! {
///     #[derive(Component!(class=ItemComponent))]
///     struct Item<T> {
///         context: T
///     }
/// }
///
/// // ...
///
/// # fn main() {
/// let mut arena_u8 = Arena::new();
/// let _ = arena_u8.insert(|id| (Item { context: 7u8 }, id));
///
/// let mut arena_u32 = Arena::new();
/// let _ = arena_u32.insert(|id| (Item { context: 7u32 }, id));
/// # }
/// ```
#[macro_export]
macro_rules! Component {
    (
        ($($arg:tt)*)
        $vis:vis enum $name:ident
        $($token:tt)+
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @args
                [, $($arg)*]
                [] []
                [$vis] [$name]
            }
            $($token)+
        }
    };
    (
        ($($arg:tt)*)
        $vis:vis struct $name:ident
        $($token:tt)+
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @args
                [, $($arg)*]
                [] []
                [$vis] [$name]
            }
            $($token)+
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! Component_impl {
   (
        @args
        [$(,)?]
        [$($class:ident)?] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::Component_impl! {
            @impl [$vis] [$name] [$($class)?] [$($alloc)?]
            [$($g)*] [$($r)*] [$($w)*]
        }
    };
    (
        @args
        [, alloc = $alloc:ty $(, $($token:tt)*)?]
        [$($class:ident)?] []
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::Component_impl! {
            @args
            [$(, $($token)*)?]
            [$($class)?] [$alloc]
            [$vis] [$name] [$($g)*] [$($r)*] [$($w)*]
        }
    };
    (
        @args
        [, alloc = $alloc:ty $(, $($token:tt)*)?]
        [$($class:ident)?] [$alloc_:ty]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::std_compile_error!("duplicated 'alloc' parameter");
    };
    (
        @args
        [, alloc = $($token:tt)*]
        [$($class:ident)?] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::std_compile_error!("invalid 'alloc' parameter");
    };
    (
        @args
        [, class = $class:ident $($token:tt)*]
        [] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::Component_impl! {
            @args
            [$($token)*]
            [$class] [$($alloc)?]
            [$vis] [$name] [$($g)*] [$($r)*] [$($w)*]
        }
    };
    (
        @args
        [, class = $class:ident $($token:tt)*]
        [$class_:ident] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::std_compile_error!("duplicated 'class' parameter");
    };
    (
        @args
        [, class = $token:tt $($tail:tt)*]
        [$($class:ident)?] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::unexpected_token!($token);
        $crate::std_compile_error!("invalid 'class' parameter");
    };
    (
        @args
        [, class = ]
        [$($class:ident)?] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::std_compile_error!("invalid 'class' parameter");
    };
    (
        @args
        [, $param:ident = $($token:tt)*]
        [$($class:ident)?] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::unexpected_token!($param);
        $crate::std_compile_error!($crate::std_concat!("unknown '", $crate::std_stringify!($param), "' parameter"));
    };
    (
        @args
        [, $token:tt $($tail:tt)*]
        [$($class:ident)?] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::unexpected_token!($token);
        $crate::std_compile_error!("invalid parameter");
    };
    (
        @args
        [$token:tt $($tail:tt)*]
        [$($class:ident)?] [$($alloc:ty)?]
        [$vis:vis] [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::unexpected_token!($token);
        $crate::std_compile_error!("comma expected");
    };
    (
        @impl [$vis:vis] [$name:ident] [] [$($alloc:ty)?] [] [] []
    ) => {
        $crate::Component_impl! { @self [$name] [$($alloc)?] }
    };
    (
        @impl [$vis:vis] [$name:ident] [$class:ident] [$($alloc:ty)?] [] [] []
    ) => {
        $crate::Component_impl! { @class [$vis] [$name] [$class] [$($alloc)?] [] [] [] }
    };
    (
        @impl [$vis:vis] [$name:ident] [] [$($alloc:ty)?] [$($g:tt)+] [$($r:tt)+] [$($w:tt)*]
    ) => {
        $crate::std_compile_error!($crate::std_concat!(
            "\
                generic component requires separate non-generic component class; \
                consider adding 'class' parameter: '#[derive(Component!(class=\
            ",
            $crate::std_stringify!($name),
            "Class)]'"
        ));
    };
    (
        @impl
        [$vis:vis] [$name:ident] [$class:ident]
        [$($alloc:ty)?] $g:tt $r:tt $w:tt
    ) => {
        $crate::Component_impl! { @class [$vis] [$name] [$class] [$($alloc)?] $g $r $w }
    };
    (
        @self [$name:ident] [$($alloc:ty)?]
    ) => {
        impl $crate::ComponentClass for $name {
            fn token() -> &'static $crate::ComponentClassToken {
                static TOKEN: $crate::ComponentClassToken = $crate::ComponentClassToken::new();
                &TOKEN
            }
        }

        impl $crate::Component for $name {
            type Class = Self;

            $(
                type Alloc = $alloc;
            )?
        }
    };
    (
        @class
        [$vis:vis] [$name:ident] [$class:ident]
        [$($alloc:ty)?] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*]
    ) => {
        $vis enum $class { }

        impl $crate::ComponentClass for $class {
            fn token() -> &'static $crate::ComponentClassToken {
                static TOKEN: $crate::ComponentClassToken = $crate::ComponentClassToken::new();
                &TOKEN
            }
        }

        impl $($g)* $crate::Component for $name $($r)* $($w)* {
            type Class = $class;

            $(
                type Alloc = $alloc;
            )?
        }
    };
}

/// [Macro attribute](https://crates.io/crates/macro-attr-2018)
/// for deriving [`ComponentId`](trait@ComponentId) trait.
///
/// Accepts input in any of following forms:
///
/// ```ignore
/// ()
/// $vis:vis struct $name:ident (
///     $(#[$id_attr:meta])* $(pub)? $id:ty
///     $(, $(#[$phantom_attr:meta])* $(pub)? $phantom:ty)* $(,)?
/// );
/// ```
///
/// ```ignore
/// ()
/// $vis:vis struct $name:ident <$generics> (
///     $(#[$id_attr:meta])* $(pub)? $id:ty
///     $(, $(#[$phantom_attr:meta])* $(pub)? $phantom:ty)* $(,)?
/// ) $(where $where_clause)?;
/// ```
///
/// # Examples
///
/// ```rust
/// # use educe::Educe;
/// # use macro_attr_2018::macro_attr;
/// use components_arena::{Component, Id, NewtypeComponentId};
/// use phantom_type::PhantomType;
///
/// # macro_attr! {
/// #    #[derive(Component!(class=ItemNodeComponent))]
/// #    struct ItemNode<Tag> {
/// #        /* ... */
/// #        tag: Tag
/// #    }
/// # }
/// #
/// macro_attr! {
///     #[derive(Educe, NewtypeComponentId!)]
///     #[educe(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
///     pub struct Item<Tag, X>(Id<ItemNode<Tag>>, PhantomType<X>);
/// }
/// ```
#[macro_export]
macro_rules! NewtypeComponentId {
    (
        ()
        $vis:vis struct $name:ident $($token:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::NewtypeComponentId_impl {
                [$name]
            }
            $($token)*
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! NewtypeComponentId_impl {
    (
        [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*] (
            $(#[$id_attr:meta])* $(pub)? $id:ty
            $(, $(#[$phantom_attr:meta])* $(pub)? $phantom:ty)* $(,)?
        );
    ) => {
        impl $($g)* $crate::ComponentId for $name $($r)* $($w)* {
            fn from_raw(raw: $crate::RawId) -> Self {
                $name(
                    <$id as $crate::ComponentId>::from_raw(raw)
                    $(, <$phantom as $crate::std_default_Default>::default())*
                )
            }

            fn into_raw(self) -> $crate::RawId {
                <$id as $crate::ComponentId>::into_raw(self.0)
            }
        }
    };
    (
        [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*]
        $token:tt $($tail:tt)*
    ) => {
        $crate::unexpected_token!($token);
        $crate::std_compile_error!("'NewtypeComponentId' supports deriving for non-empty tuple structs only");
    };
    (
        [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*]
    ) => {
        $crate::std_compile_error!("'NewtypeComponentId' supports deriving for non-empty tuple structs only");
    };
}

#[cfg(test)]
mod test {
    use macro_attr_2018::macro_attr;
    use quickcheck_macros::quickcheck;

    use core::sync::atomic::{Ordering, AtomicI8};
    use crate::*;

    macro_attr! {
        #[derive(Component!(class=GenericOneArgComponent))]
        struct GenericOneArg<T>(T);
    }
 
    macro_attr! {
        #[derive(Component!(class=GenericTwoArgsComponent))]
        struct GenericTwoArgs<A, B>(A, B);
    }

    macro_attr! {
        #[derive(Component!)]
        struct Test {
            this: Id<Test>,
            value: i8
        }
    }

    const fn _new_test_arena() -> Arena<Test> {
        Arena::new()
    }

    macro_attr! {
        #[derive(Component!)]
        struct TestWithDrop {
            value: i8
        }
    }

    static TEST_DROP: AtomicI8 = AtomicI8::new(-1);

    const fn _new_test_with_drop_arena() -> Arena<TestWithDrop> {
        Arena::new()
    }

    impl Drop for TestWithDrop {
        fn drop(&mut self) {
            TEST_DROP.store(self.value, Ordering::SeqCst);
        }
    }

    #[quickcheck]
    fn new_arena_min_capacity_is_zero(capacity: Option<u8>) -> bool {
        let capacity = capacity.map(|capacity| capacity as usize);
        capacity.map_or_else(
            || <Arena::<Test>>::new(),
            |capacity| <Arena::<Test>>::with_capacity(capacity)
        ).items().min_capacity() == 0
    }

    #[quickcheck]
    fn arena_contains_inserted_item(capacity: Option<u8>, value: i8) -> bool {
        let capacity = capacity.map(|capacity| capacity as usize);
        let mut arena = capacity.map_or_else(
            || Arena::new(),
            |capacity| Arena::with_capacity(capacity)
        );
        let id = arena.insert(|this| (Test { this, value }, this));
        arena[id].this == id && arena[id].value == value
    }

    #[should_panic]
    #[test]
    fn foreign_id_cause_panic() {
        let mut arena = Arena::new();
        let id = arena.insert(|this| (Test { this, value: 7 }, this)).into_raw();
        let id = Id::from_raw((id.0, unsafe { NonZeroUsize::new_unchecked(17) }));
        let _ = &arena[id];
    }

    #[test]
    fn drop_components() {
        {
            let mut arena = Arena::new();
            arena.insert(|this| (TestWithDrop { value: 7 }, this)).into_raw();
            TEST_DROP.store(-1, Ordering::SeqCst);
        }
        assert_eq!(TEST_DROP.load(Ordering::SeqCst), 7);
    }

    macro_attr! {
        #[derive(NewtypeComponentId!, Educe)]
        #[educe(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
        struct IdWrap1(#[allow(dead_code)] Id<Test>);
    }

    macro_attr! {
        #[derive(NewtypeComponentId!, Educe)]
        #[educe(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
        struct IdWrap2<X>(Id<Test>, PhantomType<X>);
    }

    macro_attr! {
        #[derive(NewtypeComponentId!, Educe)]
        #[educe(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
        struct IdWrap3<X, Y: Copy>(Id<Test>, PhantomType<X>, PhantomType<Y>);
    }

    macro_attr! {
        #[derive(NewtypeComponentId!, Educe)]
        #[educe(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
        struct IdWrap4<X, Y: Copy>((), PhantomType<X>, PhantomType<Y>);
    }
}

#[cfg(all(test, feature="nightly"))]
mod test_nightly {
    use macro_attr_2018::macro_attr;
    use crate::*;

    macro_attr! {
        #[derive(Component!(alloc=&'static dyn Allocator))]
        struct TestComponent {
        }
    }
}
