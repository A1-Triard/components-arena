//! **Crate features**
//!
//! * `"nightly"`
//! Enabled by default. Disable to make the library compatible with stable and beta Rust channels.

#![deny(warnings)]
#![allow(clippy::type_complexity)]
#![doc(test(attr(deny(warnings))))]
#![doc(test(attr(allow(dead_code))))]
#![doc(test(attr(allow(unused_variables))))]

#![cfg_attr(feature="nightly", feature(const_trait_impl))]

#![no_std]

include!("doc_test_readme.include");

extern crate alloc;

#[doc(hidden)]
pub use core::compile_error as std_compile_error;
#[doc(hidden)]
pub use core::default::Default as std_default_Default;
#[doc(hidden)]
pub use core::option::Option as std_option_Option;
#[cfg(feature="dyn-context")]
#[doc(hidden)]
pub use dyn_context::state::State as dyn_context_state_State;
#[cfg(feature="dyn-context")]
#[doc(hidden)]
pub use dyn_context::state::StateExt as dyn_context_state_StateExt;
#[doc(hidden)]
pub use generics::parse as generics_parse;

use alloc::collections::TryReserveError;
use alloc::vec::{self, Vec};
use core::fmt::Debug;
use core::hint::unreachable_unchecked;
use core::iter::{self, FusedIterator};
use core::mem::replace;
use core::num::{NonZeroUsize};
use core::ops::{Index, IndexMut};
use core::slice::{self};
use core::sync::atomic::{AtomicUsize, Ordering};
#[cfg(feature="dyn-context")]
use dyn_context::impl_stop;
#[cfg(feature="dyn-context")]
use dyn_context::state::State;
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

    #[cfg(feature="dyn-context")]
    fn as_component_stop() -> Option<&'static dyn ComponentStop<Component=Self>> { None }
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

/// A (mostly readonly) inner container holding [`Arena`](Arena) items.
/// While [`Arena`](Arena) itself is unique (i.e. non-clonable) object,
/// arena ['items'](Arena::items) could be cloned.
#[derive(Debug, Clone)]
pub struct ArenaItems<C: Component> {
    vec: Vec<Either<Option<usize>, (NonZeroUsize, C)>>,
    vacancy: Option<usize>,
}

impl<C: Component> ArenaItems<C> {
    #[cfg(feature="dyn-context")]
    fn clear(&mut self) {
        self.vacancy = None;
        self.vec.clear();
    }

    const fn new() -> Self {
        ArenaItems {
            vec: Vec::new(),
            vacancy: None
        }
    }

    fn with_capacity(capacity: usize) -> Self {
        ArenaItems {
            vec: Vec::with_capacity(capacity),
            vacancy: None
        }
    }

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
    iter::Enumerate<vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>>>
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
    vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>>
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
    iter::Enumerate<vec::IntoIter<Either<Option<usize>, (NonZeroUsize, C)>>>
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

/// Unordered container with random access.
#[derive(Debug)]
pub struct Arena<C: Component + 'static> {
    guard_rng: Option<SmallRng>,
    items: ArenaItems<C>,
}

impl<C: Component> Arena<C> {
    /// Creates an arena instance.
    pub const fn new() -> Self {
        Arena {
            guard_rng: None,
            items: ArenaItems::new()
        }
    }

    /// Creates an arena instance with the specified initial capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Arena {
            guard_rng: None,
            items: ArenaItems::with_capacity(capacity)
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
    pub fn into_items(mut self) -> ArenaItems<C> { replace(&mut self.items, ArenaItems::new()) }

    /// Returns reference to contained items packed in a special container.
    /// While arena itself is unique (i.e. non-clonable) object,
    /// this special container could be cloned.
    pub fn items(&self) -> &ArenaItems<C> { &self.items }

    /// Returns mutable reference to contained items packed in
    /// a (mostly readonly) special container.
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
    /// The arena tries to detect invalid provided id (i. e. foreign, or previously dropped),
    /// and panics if such detection hits. But it is important to pay respect to the fact
    /// there is small probability that invalid id will not be intercepted.
    pub fn remove(&mut self, id: Id<C>) -> C {
        match replace(&mut self.items.vec[id.index], Left(self.items.vacancy)) {
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

pub trait ComponentAspect {
    type Component: Component;
}

#[cfg(feature="dyn-context")]
pub trait ComponentStop: ComponentAspect {
    fn get<'a>(&self, state: &'a dyn State) -> &'a Arena<Self::Component>;
    fn get_mut<'a>(&self, state: &'a mut dyn State) -> &'a mut Arena<Self::Component>;
    fn stop(&self, state: &mut dyn State, id: Id<Self::Component>);
}

#[cfg(feature="dyn-context")]
impl_stop!(<C: Component + 'static> for Arena<C> {
    fn is_stopped(&self) -> bool { self.items.is_empty() || C::as_component_stop().is_none() }

    fn stop(state: &mut dyn State) {
        if let Some(component_stop) = C::as_component_stop() {
            let arena = component_stop.get(state);
            let ids = arena.items().ids().collect::<Vec<_>>();
            for id in ids {
                component_stop.stop(state, id);
            }
            let arena = component_stop.get_mut(state);
            arena.items.clear();
        }
    }
});

/// [Macro attribute](https://crates.io/crates/macro-attr-2018) for deriving [`Component`](trait@Component) trait.
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
        ()
        $vis:vis enum $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [] []
            }
            $($body)*
        }
    };
    (
        (class=$class:ident)
        $vis:vis enum $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [$class] []
            }
            $($body)*
        }
    };
    (
        (stop=$stop:ident)
        $vis:vis enum $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [] [$stop]
            }
            $($body)*
        }
    };
    (
        (class=$class:ident, stop=$stop:ident)
        $vis:vis enum $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [$class] [$stop]
            }
            $($body)*
        }
    };
    (
        (stop=$stop:ident, class=$class:ident)
        $vis:vis enum $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [$class] [$stop]
            }
            $($body)*
        }
    };
    (
        ()
        $vis:vis struct $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [] []
            }
            $($body)*
        }
    };
    (
        (class=$class:ident)
        $vis:vis struct $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [$class] []
            }
            $($body)*
        }
    };
    (
        (stop=$stop:ident)
        $vis:vis struct $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [] [$stop]
            }
            $($body)*
        }
    };
    (
        (class=$class:ident, stop=$stop:ident)
        $vis:vis struct $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [$class] [$stop]
            }
            $($body)*
        }
    };
    (
        (stop=$stop:ident, class=$class:ident)
        $vis:vis struct $name:ident
        $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::Component_impl {
                @impl [$vis] [$name] [$class] [$stop]
            }
            $($body)*
        }
    };
}


#[doc(hidden)]
#[macro_export]
macro_rules! Component_impl {
    (
        @impl [$vis:vis] [$name:ident] [] [$($stop:ident)?] [] [] [] $($body:tt)*
    ) => {
        $crate::Component_impl! { @self [$name] [$($stop)?] }
    };
    (
        @impl [$vis:vis] [$name:ident] [$class:ident] [$($stop:ident)?] [] [] [] $($body:tt)*
    ) => {
        $crate::Component_impl! { @class [$vis] [$name] [$class] [$([$stop] [] [] [])?] [] [] [] }
    };
    (
        @impl [$vis:vis] [$name:ident] [] [$($stop:ident)?] [$($g:tt)+] [$($r:tt)+] [$($w:tt)*] $($body:tt)*
    ) => {
        $crate::std_compile_error!("\
            generic component requires separate non-generic component class; \
            consider adding 'class' parameter: '#[derive(Component!(class=$class)'\
        ");
    };
    (
        @impl [$vis:vis] [$name:ident] [$class:ident] [$($stop:ident)?] $g:tt $r:tt $w:tt $($body:tt)*
    ) => {
        $crate::Component_impl! { @class [$vis] [$name] [$class] [$([$stop] $g $r $w)?] $g $r $w }
    };
    (
        @self [$name:ident] [$($stop:ident)?]
    ) => {
        impl $crate::ComponentClass for $name {
            fn token() -> &'static $crate::ComponentClassToken {
                static TOKEN: $crate::ComponentClassToken = $crate::ComponentClassToken::new();
                &TOKEN
            }
        }

        $(
            struct $stop;

            impl $crate::ComponentAspect for $stop {
                type Component = $name;
            }
        )?

        impl $crate::Component for $name {
            type Class = Self;

            $(
                fn as_component_stop() -> $crate::std_option_Option<&'static dyn $crate::ComponentStop<Component=Self>> {
                    const COMPONENT_STOP: $stop = $stop;
                    $crate::std_option_Option::Some(&COMPONENT_STOP)
                }
            )?
        }
    };
    (
        @class
        [$vis:vis] [$name:ident] [$class:ident]
        [$([$stop:ident] [$($g_:tt)*] [$($r_:tt)*] [$($w_:tt)*])?]
        [$($g:tt)*] [$($r:tt)*] [$($w:tt)*]
    ) => {
        $vis enum $class { }

        impl $crate::ComponentClass for $class {
            fn token() -> &'static $crate::ComponentClassToken {
                static TOKEN: $crate::ComponentClassToken = $crate::ComponentClassToken::new();
                &TOKEN
            }
        }

        $(
            struct $stop;

            impl $($g_)* $crate::ComponentAspect for $stop $($w_)* {
                type Component = $name $($r_)*;
            }
        )?

        impl $($g)* $crate::Component for $name $($r)* $($w)* {
            type Class = $class;

            $(
                fn as_component_stop() -> $crate::std_option_Option<&'static dyn $crate::ComponentStop<Component=Self>> {
                    const COMPONENT_STOP: $stop = $stop;
                    $crate::std_option_Option::Some(&COMPONENT_STOP)
                }
            )?
        }
    };
}

/// [Macro attribute](https://crates.io/crates/macro-attr-2018)
/// for deriving [`ComponentId`](trait@ComponentId) trait.
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
        $vis:vis struct $name:ident $($body:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::NewtypeComponentId_impl {
                [$name]
            }
            $($body)*
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! NewtypeComponentId_impl {
    (
        [$name:ident] [$($g:tt)*] [$($r:tt)*] [$($w:tt)*]
        ($(pub)? $id:ty $(, $(pub)? $phantom:ty)* $(,)?);
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
        $($body:tt)*
    ) => {
        $crate::std_compile_error!("'NewtypeComponentId' deriving is supported for non-empty tuple structs only");
    };
}

#[macro_export]
macro_rules! arena_newtype {
    (
        $arena_newtype:ty
    ) => {
        fn get<'a>(
            &self,
            state: &'a dyn $crate::dyn_context_state_State
        ) -> &'a $crate::Arena<<Self as $crate::ComponentAspect>::Component> {
            &<dyn $crate::dyn_context_state_State as $crate::dyn_context_state_StateExt>::get::<$arena_newtype>(state).0
        }

        fn get_mut<'a>(
            &self,
            state: &'a mut dyn $crate::dyn_context_state_State
        ) -> &'a mut $crate::Arena<<Self as $crate::ComponentAspect>::Component> {
            &mut <dyn $crate::dyn_context_state_State as $crate::dyn_context_state_StateExt>::get_mut::<$arena_newtype>(state).0
        }
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

    static TEST_DROP: AtomicI8 = AtomicI8::new(-1);

    impl Drop for Test {
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
            arena.insert(|this| (Test { this, value: 7 }, this)).into_raw();
            TEST_DROP.store(-1, Ordering::SeqCst);
        }
        assert_eq!(TEST_DROP.load(Ordering::SeqCst), 7);
    }

    macro_attr! {
        #[derive(NewtypeComponentId!, Educe)]
        #[educe(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
        struct IdWrap1(Id<Test>);
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

#[cfg(all(test, feature="dyn-context"))]
mod test_dyn_context {
    use dyn_context::NewtypeStop;
    use dyn_context::state::State;
    use macro_attr_2018::macro_attr;
    use crate::*;

    macro_attr! {
        #[derive(NewtypeStop!)]
        struct TestStopArena(Arena<TestStop>);
    }

    macro_attr! {
        #[derive(Component!(stop=TestStopImpl))]
        struct TestStop {
            stop: bool
        }
    }

    impl ComponentStop for TestStopImpl {
        arena_newtype!(TestStopArena);

        fn stop(&self, state: &mut dyn State, id: Id<Self::Component>) {
            self.get_mut(state)[id].stop = true;
        }
    }
}
