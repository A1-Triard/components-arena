impl<C: Component> ComponentId for Id<C> {
    fn from_raw(raw: RawId) -> Self {
        Id { index: raw.0, guard: raw.1, phantom: PhantomType::new() }
    }

    fn into_raw(self) -> RawId {
        (self.index, self.guard)
    }
}
