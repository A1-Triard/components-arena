impl<C: Component> Arena<C> {
    /// Creates an arena instance.
    pub const fn new() -> Self where C::Alloc: ~const Default {
        Self::new_in(Default::default())
    }

    /// Creates an arena instance with the specified initial capacity.
    pub fn with_capacity(capacity: usize) -> Self where C::Alloc: Default {
        Self::with_capacity_in(capacity, Default::default())
    }
}
