#![deny(warnings)]
#![cfg_attr(feature="nightly", feature(const_fn))]
#![cfg_attr(feature="nightly", feature(try_reserve))]
#![cfg_attr(feature="nightly", feature(shrink_to))]

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

#[cfg(test)]
#[macro_use]
extern crate macro_attr;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(feature="nightly")]
use std::collections::TryReserveError;
use std::fmt::Debug;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::replace;
use std::num::{NonZeroUsize};
use std::ops::{Index, IndexMut};
#[cfg(feature="std")]
use std::panic::{UnwindSafe, RefUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::vec::Vec;
use either::{Either, Left, Right};
use rand::rngs::SmallRng;
use rand::{RngCore, SeedableRng};
#[cfg(all(feature="std", feature="nightly"))]
use once_cell::sync::{self};
#[cfg(all(feature="std", feature="nightly"))]
use std::sync::Mutex;
#[cfg(all(feature="std", feature="nightly"))]
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
/// Also it should be garanteed that no other `ComponentClass` implementation
/// returns same `ComponentClassLock` instance.
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

unsafe impl<C: Component> Send for Id<C> { }
unsafe impl<C: Component> Sync for Id<C> { }
impl<C: Component> Unpin for Id<C> { }
#[cfg(feature="std")]
impl<C: Component> RefUnwindSafe for Id<C> { }
#[cfg(feature="std")]
impl<C: Component> UnwindSafe for Id<C> { }

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
///     let id = arena.insert(|id| (MyComponent { /* ... */ }, id));
/// }
/// ```
///
/// In the `no_std` environment a custom solution should be used to store `ComponentClassToken`.
pub struct ComponentClassToken<C: ComponentClass> {
    tag_seed_rng: SmallRng,
    phantom: PhantomData<C>
}

unsafe impl<C: ComponentClass> Send for ComponentClassToken<C> { }
unsafe impl<C: ComponentClass> Sync for ComponentClassToken<C> { }
impl<C: ComponentClass> Unpin for ComponentClassToken<C> { }
#[cfg(feature="std")]
impl<C: ComponentClass> RefUnwindSafe for ComponentClassToken<C> { }
#[cfg(feature="std")]
impl<C: ComponentClass> UnwindSafe for ComponentClassToken<C> { }

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
    /// Creates an arena instance.
    pub fn new(class: &mut ComponentClassToken<C::Class>) -> Self {
        Arena {
            tag_rng: SmallRng::seed_from_u64(class.tag_seed_rng.next_u64()),
            items: Vec::new(),
            vacancy: None
        }
    }

    /// Creates an arena instance with the specified initial capacity.
    pub fn with_capacity(capacity: usize, class: &mut ComponentClassToken<C::Class>) -> Self {
        Arena {
            tag_rng: SmallRng::seed_from_u64(class.tag_seed_rng.next_u64()),
            items: Vec::with_capacity(capacity),
            vacancy: None
        }
    }

    /// Returns the number of elements the arena can hold without reallocating.
    pub fn capacity(&self) -> usize { self.items.capacity() }


    /// Returns the maximum number of elements ever in the arena.
    ///
    /// Arena `len` never decreases.
    ///
    /// # Examples
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
    ///     assert_eq!(arena.len(), 0);
    ///     let id_1 = arena.insert(|id| (MyComponent { /* ... */ }, id));
    ///     assert_eq!(arena.len(), 1);
    ///     let id_2 = arena.insert(|id| (MyComponent { /* ... */ }, id));
    ///     assert_eq!(arena.len(), 2);
    ///     arena.remove(id_1);
    ///     assert_eq!(arena.len(), 2);
    ///     let id_3 = arena.insert(|id| (MyComponent { /* ... */ }, id));
    ///     assert_eq!(arena.len(), 2);
    ///     let id_4 = arena.insert(|id| (MyComponent { /* ... */ }, id));
    ///     assert_eq!(arena.len(), 3);
    /// }
    /// ```
    pub fn len(&self) -> usize { self.items.len() }

    /// Reserves capacity for at least `additional` more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `reserve`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    pub fn reserve(&mut self, additional: usize) { self.items.reserve(additional) }

    /// Reserves the minimum capacity for exactly `additional` more elements.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore, capacity can not be relied upon to be precisely minimal.
    /// Prefer `reserve` if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    pub fn reserve_exact(&mut self, additional: usize) { self.items.reserve_exact(additional) }

    /// Shrinks the capacity of the arena with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length and the supplied value.
    #[cfg(feature="nightly")]
    pub fn shrink_to(&mut self, min_capacity: usize) { self.items.shrink_to(min_capacity) }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator
    /// may still inform the arena that there is space for a few more elements.
    pub fn shrink_to_fit(&mut self) { self.items.shrink_to_fit() }

    /// Tries to reserve capacity for at least additional more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `try_reserve`, capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    #[cfg(feature="nightly")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.items.try_reserve(additional)
    }

    /// Tries to reserve capacity for exactly additional more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore, capacity can not be relied upon to be precisely minimal.
    /// Prefer `try_reserve` if future insertions are expected.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    #[cfg(feature="nightly")]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.items.try_reserve_exact(additional)
    }

    /// Place new component into the arena.
    ///
    /// # Examples
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
    /// fn main() {
    ///     let mut arena = Arena::new(&mut MY_COMPONENT.lock().unwrap());
    ///     let new_component_id = arena.insert(|id| (MyComponent { /* ... */ }, id));
    /// }
    /// ```
    pub fn insert<T>(&mut self, component: impl FnOnce(Id<C>) -> (C, T)) -> T {
        let mut tag = 0usize.to_le_bytes();
        self.tag_rng.fill_bytes(&mut tag[..]);
        let tag = NonZeroUsize::new(usize::from_le_bytes(tag)).unwrap_or(unsafe { NonZeroUsize::new_unchecked(43) });
        if let Some(index) = self.vacancy {
            let id = Id { index, tag, phantom: PhantomData };
            let (component, result) = component(id);
            let item = (tag, component);
            self.vacancy = replace(&mut self.items[index], Right(item)).left()
                .unwrap_or_else(|| unsafe { unreachable_unchecked() });
            result
        } else {
            let index = self.items.len();
            let id = Id { index, tag, phantom: PhantomData };
            let (component, result) = component(id);
            let item = (tag, component);
            self.items.push(Right(item));
            result
        }
    }

    /// Removes component with provided id.
    ///
    /// The arena tries to detect invalid provided id (i. e. foreign, or previously dropped),
    /// and panics if such detection hits. But it is important to pay respect to the fact
    /// there is small probability that invalid id will not be intercepted.
    pub fn remove(&mut self, id: Id<C>) -> C {
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
#[cfg(all(feature="std", feature="nightly"))]
pub struct ComponentClassMutex<C: ComponentClass>(sync::Lazy<Mutex<ComponentClassToken<C>>>);

#[cfg(all(feature="std", feature="nightly"))]
impl<C: ComponentClass> ComponentClassMutex<C> {
    pub const fn new() -> Self {
        ComponentClassMutex(sync::Lazy::new(|| Mutex::new(
            ComponentClassToken::new().expect("component class token already crated")
        )))
    }
}

#[cfg(all(feature="std", feature="nightly"))]
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
///     let id = arena.insert(|id| (Item { /* ... */ }, id));
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
///     let _ = arena_u8.insert(|id| (Item { context: 7u8 }, id));
///
///     let mut arena_u32 = Arena::new(&mut ITEM.lock().unwrap());
///     let _ = arena_u32.insert(|id| (Item { context: 7u32 }, id));
/// }
/// ```
#[macro_export]
macro_rules! Component {
    (()
        $(pub $((crate))?)? enum $name:ident
        $($tail:tt)+ ) => {
        Component! {
            @impl $name
        }
    };
    (()
        $(pub $((crate))?)? struct $name:ident
        $($tail:tt)+ ) => {
        Component! {
            @impl $name
        }
    };
    ((class=$class:ident)
        enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $($tail:tt)+ ) => {
        Component! {
            @impl () $name, $class,
            [ $( $lt ),+ ],
            [ $( $lt $( : $clt $(+ $dlt )* )? ),+ ]
        }
    };
    ((class=$class:ident)
        struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $($tail:tt)+ ) => {
        Component! {
            @impl () $name, $class,
            [ $( $lt ),+ ],
            [ $( $lt $( : $clt $(+ $dlt )* )? ),+ ]
        }
    };
    ((class=$class:ident)
        pub(crate) enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $($tail:tt)+ ) => {
        Component! {
            @impl (pub(crate)) $name, $class,
            [ $( $lt ),+ ],
            [ $( $lt $( : $clt $(+ $dlt )* )? ),+ ]
        }
    };
    ((class=$class:ident)
        pub(crate) struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $($tail:tt)+ ) => {
        Component! {
            @impl (pub(crate)) $name, $class,
            [ $( $lt ),+ ],
            [ $( $lt $( : $clt $(+ $dlt )* )? ),+ ]
        }
    };
    ((class=$class:ident)
        pub enum $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $($tail:tt)+ ) => {
        Component! {
            @impl (pub) $name, $class,
            [ $( $lt ),+ ],
            [ $( $lt $( : $clt $(+ $dlt )* )? ),+ ]
        }
    };
    ((class=$class:ident)
        pub struct $name:ident
        < $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ > $($tail:tt)+ ) => {
        Component! {
            @impl (pub) $name, $class,
            [ $( $lt ),+ ],
            [ $( $lt $( : $clt $(+ $dlt )* )? ),+ ]
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
    (@impl ($($p:tt $($c:tt)?)?) $name:ident, $class:ident, [ $($g:tt)+ ], [ $($r:tt)+ ]) => {
        $($p $($c)?)? enum $class { }
        impl $crate::ComponentClass for $class {
            fn lock() -> &'static $crate::ComponentClassLock {
                static LOCK: $crate::ComponentClassLock = $crate::ComponentClassLock::new();
                &LOCK
            }
        }
        impl < $($g)+ > $crate::Component for $name < $($r)+ > {
            type Class = $class;
        }
    };
}

#[cfg(test)]
mod test {
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

    static TEST: ComponentClassMutex<Test> = ComponentClassMutex::new();

    #[quickcheck]
    fn new_arena_len_is_zero(capacity: Option<usize>) -> bool {
        capacity.map_or_else(
            || <Arena::<Test>>::new(&mut TEST.lock().unwrap()),
            |capacity| <Arena::<Test>>::with_capacity(capacity, &mut TEST.lock().unwrap())
        ).len() == 0
    }

    #[quickcheck]
    fn arena_contains_inserted_item(capacity: Option<usize>, value: i8) -> bool {
        let mut arena = capacity.map_or_else(
            || Arena::new(&mut TEST.lock().unwrap()),
            |capacity| Arena::with_capacity(capacity, &mut TEST.lock().unwrap())
        );
        let id = arena.insert(|this| (Test { this, value }, this));
        arena[id].this == id && arena[id].value == value
    }
}
