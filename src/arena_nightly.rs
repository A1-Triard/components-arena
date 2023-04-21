impl<C: Component> Arena<C> {
    /// Creates an arena instance.
    pub const fn new() -> Self where C::Alloc: ~const ConstDefault {
        Self::new_in(ConstDefault::default_const())
    }

    /// Creates an arena instance with the specified initial capacity.
    pub fn with_capacity(capacity: usize) -> Self where C::Alloc: ConstDefault {
        Self::with_capacity_in(capacity, ConstDefault::default_const())
    }
}
