#[macro_use]
extern crate derivative;

use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;
use std::hash::Hash;

pub unsafe trait Component {
    type Id: Debug + Copy + Eq + Hash + Ord;
    type Index: Debug + Copy + Eq + Hash + Ord + TryInto<usize> + TryFrom<usize>;
    unsafe fn new_id() -> Self::Id;
}

#[macro_export]
macro_rules! Component {
    ((Index=u32, ID=$id:ident) $(pub)* struct $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? { $($tail:tt)* } ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u32, ::std::num::NonZeroU64, ::std::sync::atomic::AtomicU64
        }
    };
    ((Index=u16, ID=$id:ident) $(pub)* struct $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? { $($tail:tt)* } ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u16, ::std::num::NonZeroU32, ::std::sync::atomic::AtomicU32
        }
    };
    ((Index=u32, ID=$id:ident) $(pub)* struct $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? ( $($tail:tt)* ) ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u32, ::std::num::NonZeroU64, ::std::sync::atomic::AtomicU64
        }
    };
    ((Index=u16, ID=$id:ident) $(pub)* struct $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? ( $($tail:tt)* ) ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u16, ::std::num::NonZeroU32, ::std::sync::atomic::AtomicU32
        }
    };
    ((Index=u32, ID=$id:ident) $(pub)* enum $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? { $($tail:tt)* } ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u32, ::std::num::NonZeroU64, ::std::sync::atomic::AtomicU64
        }
    };
    ((Index=u16, ID=$id:ident) $(pub)* enum $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? { $($tail:tt)* } ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u16, ::std::num::NonZeroU32, ::std::sync::atomic::AtomicU32
        }
    };
    ((ID=$id:ident, Index=u32) $(pub)* struct $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? { $($tail:tt)* } ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u32, ::std::num::NonZeroU64, ::std::sync::atomic::AtomicU64
        }
    };
    ((ID=$id:ident, Index=u16) $(pub)* struct $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? { $($tail:tt)* } ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u16, ::std::num::NonZeroU32, ::std::sync::atomic::AtomicU32
        }
    };
    ((ID=$id:ident, Index=u32) $(pub)* struct $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? ( $($tail:tt)* ) ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u32, ::std::num::NonZeroU64, ::std::sync::atomic::AtomicU64
        }
    };
    ((ID=$id:ident, Index=u16) $(pub)* struct $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? ( $($tail:tt)* ) ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u16, ::std::num::NonZeroU32, ::std::sync::atomic::AtomicU32
        }
    };
    ((ID=$id:ident, Index=u32) $(pub)* enum $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? { $($tail:tt)* } ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u32, ::std::num::NonZeroU64, ::std::sync::atomic::AtomicU64
        }
    };
    ((ID=$id:ident, Index=u16) $(pub)* enum $name:ident
        $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? { $($tail:tt)* } ) => {
        Component! {
            @impl $name,
            $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?,
            $(< $( $lt ),+ >)?,
            $id, u16, ::std::num::NonZeroU32, ::std::sync::atomic::AtomicU32
        }
    };
    (@impl $name:ident, $(< $g:tt >)?, $(< $r:tt >)?, $new_id:ident, $index:ty, $id:ty, $atomic_id:ty) => {
        static $new_id: $atomic_id = <$atomic_id>::new(1);
        unsafe impl$(< $g >)? $crate::components::Component for $name $(< $r >)? {
            type Id = $id;
            type Index = $index;
            unsafe fn new_id() -> Self::Id {
                <$id>::new($new_id.fetch_add(1, ::std::sync::atomic::Ordering::Relaxed)).unwrap()
            }
        }
    };
}

#[derive(Derivative)]
#[derivative(Debug(bound=""), Copy(bound=""), Clone(bound=""), Eq(bound=""), PartialEq(bound=""))]
#[derivative(Hash(bound=""), Ord(bound=""), PartialOrd(bound=""))]
pub struct Id<C: Component> {
    index: <C as Component>::Index,
    id: <C as Component>::Id,
}

#[derive(Debug)]
pub struct Components<C: Component> {
    items: Vec<Option<(C::Id, C)>>,
    vacancies: Vec<C::Index>,
}

impl<C: Component> Components<C> {
    pub fn new() -> Self {
        Components { items: Vec::new(), vacancies: Vec::new() }
    }

    pub fn attach(&mut self, component: impl FnOnce(Id<C>) -> C) -> Id<C> {
        let id = unsafe { C::new_id() };
        if let Some(index) = self.vacancies.pop() {
            let index_id = Id { index, id };
            let item = (id, component(index_id));
            let index_as_usize = index.try_into().unwrap_or_else(|_| panic!());
            let none = self.items[index_as_usize].replace(item);
            if none.is_some() { panic!(); }
            index_id
        } else {
            let index = self.items.len().try_into().unwrap_or_else(|_| panic!());
            let index_id = Id { index, id };
            let item = (id, component(index_id));
            self.items.push(Some(item));
            index_id
        }
    }

    #[must_use]
    pub fn detach(&mut self, id: Id<C>) -> Option<C> {
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| panic!());
        if self.items.len() <= index_as_usize { return None; }
        if let Some((item_id, component)) = self.items[index_as_usize].take() {
            if item_id == id.id {
                self.vacancies.push(id.index);
                Some(component)
            } else {
                let none = self.items[index_as_usize].replace((item_id, component));
                if none.is_some() { panic!(); }
                None
            }
        } else {
            None
        }
    }

    pub fn get(&self, id: Id<C>) -> Option<&C> {
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| panic!());
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
        let index_as_usize = id.index.try_into().unwrap_or_else(|_| panic!());
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
