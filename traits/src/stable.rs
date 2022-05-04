impl ComponentId for RawId {
    fn from_raw(raw: RawId) -> Self { raw }

    fn into_raw(self) -> RawId { self }
}

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
