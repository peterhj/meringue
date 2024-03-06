pub use fnv::{FnvHashMap as FHashMap, FnvHashSet as FHashSet};
//pub use fxhash::{FxHashMap as FHashMap, FxHashSet as FHashSet};

pub use std::collections::{BTreeMap, BTreeSet};

pub mod hashtreap;

pub type HTreapMap<K, V> = self::hashtreap::HashTreapMap<K, V>;
pub type HTreapSet<K> = self::hashtreap::HashTreapSet<K>;

pub type IHTreapMap<K, V> = self::hashtreap::InlineHashTreapMap<K, V>;
pub type IHTreapSet<K> = self::hashtreap::InlineHashTreapSet<K>;

pub type IHTreapMapCloneIter<K, V> = self::hashtreap::HashTreapMapCloneIter<K, V, self::hashtreap::Record<K, V>>;
