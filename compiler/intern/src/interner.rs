use std::collections::HashMap;
use std::mem;

// use serde::{Deserialize, Serialize};

pub(super) trait StrId: Eq + Copy + Sized + Send + Sync {
    fn from_usize(index: usize) -> Self;
    fn to_usize(&self) -> usize;
}

#[derive(Debug)]
pub(crate) struct Interner<'s, S: StrId> {
    map: HashMap<&'s str, S>,
    vec: Vec<&'s str>,
    buf: String,
    all: Vec<String>,
}

impl<'s, S> Interner<'s, S>
where
    S: StrId,
{
    pub const BASE_CAPACITY: usize = 100;

    pub fn with_capacity(cap: usize) -> Self {
        let cap = cap.next_power_of_two();
        Self {
            map: HashMap::default(),
            vec: Vec::new(),
            buf: String::with_capacity(cap),
            all: Vec::new(),
        }
    }

    pub(crate) fn with_reserved<const N: usize>(strings: [&str; N]) -> Self {
        let mut this = Self::with_capacity(Self::BASE_CAPACITY);
        for s in strings {
            this.intern(s);
        }
        this
    }

    pub fn intern(&mut self, string: impl AsRef<str>) -> S {
        let string = string.as_ref();
        if let Some(&id) = self.map.get(string) {
            return id;
        }

        let string = unsafe { self.alloc(string) };
        let id = S::from_usize(self.map.len());

        self.map.insert(string, id);
        self.vec.push(string);

        id
    }

    pub fn lookup(&self, id: &S) -> &str {
        self.vec[id.to_usize()]
    }

    unsafe fn alloc(&mut self, string: &str) -> &'s str {
        let cap = self.buf.capacity();
        if cap < self.buf.len() + string.len() {
            // just doubling isn't enough -- need to ensure the new string
            // actually fits
            let new_cap = (cap.max(string.len()) + 1).next_power_of_two();
            let new_buf = String::with_capacity(new_cap);
            let old_buf = mem::replace(&mut self.buf, new_buf);
            self.all.push(old_buf);
        }

        let interned = {
            let start = self.buf.len();
            self.buf.push_str(string);
            &self.buf[start..]
        };

        &*(interned as *const str)
    }
}

macro_rules! global_string_interner {
    (
        #with_reserved
        :handle $interner_id:ident
        :key_type $key_type:path
        :module $mod_id:ident
        // $(:doc $(#[$doc:meta])+)?
        :predefined
            $(|)? 0 $(:)? $name0:ident $lit0:literal
            $(| $index:literal $(:)? $name:ident $lit:literal)*
    ) => {
        lazy_static::lazy_static! {
            static ref $interner_id: std::sync::Arc<std::sync::Mutex<crate::interner::Interner<'static, $key_type>>> = std::sync::Arc::new(std::sync::Mutex::new(crate::interner::Interner::with_reserved([
                $lit0,
                $($lit,)*
            ])));
        }

        global_string_interner! {
            mod $mod_id const $key_type = $name0 $($index $name)*
        }

        impl $key_type {
            #![allow(unused)]

            pub fn intern(string: impl AsRef<str>) -> Self {
                match $interner_id.lock() {
                    Ok(mut guard) => {
                        guard.intern(string).clone()
                    }
                    Err(e) => {
                        eprintln!("Poison error while interning string for interner `{}` with keys of type `{}`", stringify!($interner_id), stringify!($key_type));
                        panic!("{e}")
                    }
                }
            }

            pub fn as_str(&self) -> &str {
                let guard = $interner_id.lock().unwrap();
                // Safety: we are extending the lifetime of the
                // string, however since it is interned with a
                // `'static` lifetime, the data pointed to should
                // always be valid. CONFIRM!
                unsafe { std::mem::transmute::<_, &str>(guard.lookup(self)) }
            }

            pub fn lookup(&self) -> String {
                match $interner_id.lock() {
                    Ok(guard) => guard.lookup(self).to_string(),
                    Err(e) => {
                        eprintln!("{}", e);
                        panic!(
                            "`{}` poisoned while looking up `{}` key `{:?}`",
                            stringify!($interner_id),
                            stringify!($key_type),
                            &self.0
                        )
                    }
                }
            }

            /// Similar functionality as `lookup`, but instead of
            /// returning a string slice (and containing unsafe code),
            /// a continuation is applied to the string slice.
            pub fn map_str<S>(&self, k: impl FnOnce(&str) -> S) -> S {
                match $interner_id.lock() {
                    Ok(g) => k(g.lookup(self)),
                    Err(e) => {
                        eprintln!(
                            "Poison error while looking up string slice for symbol `{}` with continuation",
                            self.0
                        );
                        panic!("{e}")
                    }
                }
            }

            pub fn intern_nfc_normalized<S: AsRef<str>>(s: S) -> Self {
                use unicode_normalization::UnicodeNormalization;
                Self::intern(s.as_ref().nfc().collect::<String>())
            }

            pub fn intern_many<S: AsRef<str>, const N: usize>(strings: [S; N]) -> [Self; N] {
                match $interner_id.lock() {
                    Ok(mut guard) => {
                        let mut syms = [Self(0); N];
                        for (i, s) in strings.into_iter().enumerate() {
                            syms[i] = guard.intern(s.as_ref());
                        }
                        syms
                    }
                    Err(e) => {
                        eprintln!("{e}");
                        panic!(
                            "Interner<{}> `{}` poisoned while interning `{:?}`",
                            stringify!($key_type),
                            stringify!($interner_id),
                            &strings.iter().map(|s| s.as_ref()).collect::<Vec<_>>()
                        )
                    }
                }
            }

            pub fn intern_many_with<S: AsRef<str>, I, const N: usize>(
                strings: [S; N],
                mut f: impl FnMut(Self) -> I,
            ) -> [I; N] {
                match $interner_id.lock() {
                    Ok(mut guard) => {
                        let mut syms: [I; N] = unsafe { std::mem::zeroed() };
                        let mut i = 0;
                        for it in &mut syms[..] {
                            *it = f(guard.intern(strings[i].as_ref()));
                            i += 1;
                        }
                        syms
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        panic!(
                            "Interner<{}> `{}` poisoned while interning `{:?}`",
                            stringify!($key_type),
                            stringify!($interner_id),
                            &strings.iter().map(|s| s.as_ref()).collect::<Vec<_>>()
                        )
                    }
                }
            }
        }
    };
    (
        :handle $interner_id:ident
        :key_type: $key_type:path
    ) => {
        lazy_static::lazy_static! {
            static ref $interner_id: std::sync::Arc<std::sync::Mutex<Interner<'static, $key_type>>> = std::sync::Arc::new(std::sync::Mutex::new(Interner::with_capacity(Interner::BASE_CAPACITY)));
        }
    };
    (mod $module:ident const $key_type:path = $name0:ident $($index:literal $name:ident)*) => {
        pub mod $module {
            type Idx = $key_type;
            const fn make_idx(n: u32) -> Idx { $key_type(n) }

            #[allow(unused)]
            pub const $name0: Idx = make_idx(0);
            $(
                #[allow(unused)]
                pub const $name: Idx = make_idx($index);
            )*
        }
    };
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Key(u32);

    impl StrId for Key {
        fn from_usize(index: usize) -> Self {
            Key(index as u32)
        }

        fn to_usize(&self) -> usize {
            self.0 as usize
        }
    }

    global_string_interner! {
        #with_reserved
        :handle KEY_STORE
        :key_type crate::interner::test::Key
        :module keys
        :predefined
            | 0 FOO "foo"
            | 1 BAR "bar"
            | 2 BAZ "baz"
    }

    #[test]
    fn test_global_interner() {
        let actual_baz_key = { KEY_STORE.lock().unwrap().intern("baz") };
        let prestored_baz_key = keys::BAZ;
        assert_eq!(actual_baz_key, prestored_baz_key);
        assert_eq!(prestored_baz_key.lookup(), "baz");
    }
}
