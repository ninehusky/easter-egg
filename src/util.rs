use std::fmt;
use std::str::FromStr;
use std::sync::Mutex;

use indexmap::{IndexMap, IndexSet};
use once_cell::sync::Lazy;
use std::fmt::Formatter;
use std::iter::FromIterator;
use itertools::Itertools;
use serde::de::{Error, MapAccess};
use serde::{Deserialize, Deserializer, Serialize};
use serde::ser::SerializeMap;

pub use symbol_table::GlobalSymbol as Symbol;

pub(crate) trait JoinDisp {
    #[allow(dead_code)]
    fn disp_string(self) -> String;
    fn sep_string(self, sep: &str) -> String;
}

impl<I> JoinDisp for I where I: Iterator,
                              I::Item: fmt::Display {
    fn disp_string(self) -> String {
        self.sep_string(", ")
    }

    fn sep_string(self, sep: &str) -> String {
        self.map(|x| format!("{}", x)).join(sep)
    }
}

pub trait Singleton<T> {
    fn singleton(t: T) -> Self;
}

impl<T, FI> Singleton<T> for FI
where FI: FromIterator<T> {
    fn singleton(t: T) -> Self {
        FI::from_iter(std::iter::once(t))
    }
}



/** A data structure to maintain a queue of unique elements.

Notably, insert/pop operations have O(1) expected amortized runtime complexity.
*/
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub(crate) struct UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    set: IndexSet<T>,
    queue: std::collections::VecDeque<T>,
}

impl<T> Default for UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    fn default() -> Self {
        UniqueQueue {
            set: IndexSet::default(),
            queue: std::collections::VecDeque::new(),
        }
    }
}

#[allow(dead_code)]
impl<T> UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    pub fn insert(&mut self, t: T) {
        if self.set.insert(t.clone()) {
            self.queue.push_back(t);
        }
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for t in iter.into_iter() {
            self.insert(t);
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        let res = self.queue.pop_front();
        res.as_ref().map(|t| self.set.remove(t));
        res
    }

    pub fn is_empty(&self) -> bool {
        let r = self.queue.is_empty();
        debug_assert_eq!(r, self.set.is_empty());
        r
    }
}

impl<T> IntoIterator for UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    type Item = T;

    type IntoIter = <std::collections::VecDeque<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.queue.into_iter()
    }
}

impl<A> FromIterator<A> for UniqueQueue<A>
where
    A: Eq + std::hash::Hash + Clone,
{
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut queue = UniqueQueue::default();
        for t in iter {
            queue.insert(t);
        }
        queue
    }
}
