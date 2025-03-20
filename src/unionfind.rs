use crate::Id;
use std::fmt::Debug;
use as_any::AsAny;
use bimap::BiBTreeMap;

pub trait UnionFind<K: Copy + Eq> : AsAny + Debug + Send + Sync {

    /// Returns the number of elements in the union find.
    fn len(&self) -> usize;

    /// Finds the leader of the set that `current` is in.
    /// If K is not in the union find, it should return K.
    fn find(&self, current: K) -> K;

    /// Given two leader ids, unions the two eclasses.
    /// This should run find to compress paths for efficiency.
    /// Returns (new leader, other id found).
    /// If either root is not in the union find, it should insert it or panic.
    fn union(&mut self, root1: K, root2: K) -> (K, K);

    /// Return a boxed clone of the union find.
    fn clone_box(&self) -> Box<dyn UnionFind<K>>;

    /// Return an iterator over the leaders.
    fn iter(&self) -> Box<dyn Iterator<Item = K> + '_>;
}

impl<K> Clone for Box<dyn UnionFind<K> + 'static> where 
    K: Copy + std::cmp::Eq + 'static,
{
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

pub trait MutUnionFind<K: Copy + std::cmp::Eq>: UnionFind<K> {
    /// Finds the leader of the set that `current` is in.
    /// This version updates the parents to compress the path.
    fn find_mut(&mut self, current: K) -> K;
}

#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SimpleUnionFind {
    parents: Vec<Id>,
}

impl SimpleUnionFind {
    pub(crate) fn parent(&self, query: Id) -> Id {
        self.parents[usize::from(query)]
    }

    pub(crate) fn parent_mut(&mut self, query: Id) -> &mut Id {
        &mut self.parents[usize::from(query)]
    }

    /// Creates a new union find with a single element.
    pub fn make_set(&mut self) -> Id {
        let id = Id::from(self.parents.len());
        self.parents.push(id);
        id
    }
}

impl<'a> UnionFind<Id> for SimpleUnionFind {
    fn len(&self) -> usize {
        self.parents.len()
    }

    fn find(&self, mut current: Id) -> Id {
        while current != self.parent(current) {
            current = self.parent(current)
        }
        current
    }

    /// Given two leader ids, unions the two eclasses making root1 the leader.
    fn union(&mut self, root1: Id, root2: Id) -> (Id, Id) {
        let root1 = self.find_mut(root1);
        let root2 = self.find_mut(root2);
        if root1 > root2 {
            return self.union(root2, root1);
        }
        *self.parent_mut(root2) = root1;
        (root1, root2)
    }
    
    fn clone_box(&self) -> Box<dyn UnionFind<Id>> {
        Box::new(self.clone())
    }
    
    fn iter(&self) -> Box<dyn Iterator<Item = Id> + '_> {
        let it = self.parents.iter()
            .enumerate()
            .filter(|(i, p)| *i == (p.0 as usize))
            .map(|(_, p)| *p);
        Box::new(it)
    }
}

impl MutUnionFind<Id> for SimpleUnionFind {
    fn find_mut(&mut self, mut current: Id) -> Id {
        let mut collected = vec![];
        while current != self.parent(current) {
            collected.push(current);
            current = self.parent(current);
        }
        for c in collected {
            *self.parent_mut(c) = current;
        }
        current
    }
}

impl SimpleUnionFind {
    pub(crate) fn union_no_swap(&mut self, root1: Id, root2: Id) -> (Id, Id) {
        let root1 = self.find_mut(root1);
        let root2 = self.find_mut(root2);
        *self.parent_mut(root2) = root1;
        (root1, root2)
    }
}

/// Data inside the union find wrapper should implement a merge function.
pub trait Merge {
    fn merge(&mut self, other: Self);
}

impl Merge for () {
    fn merge(&mut self, _: Self) {}
}

/// A wrapper for other union find implementations [U].
/// This "translates" keys [K] to the internal representation so that external api can use any key.
/// It also holds an object [T] for each equivalence class which is unioned with the [merge] function.
/// It won't implement the union find api right now because I don't want to change it at the moment
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct UnionFindWrapper<K: Copy + Ord> {
    uf: SimpleUnionFind,
    trns: BiBTreeMap<K, usize>
}

impl<K: Copy + Ord + Debug + Send + Sync + 'static> UnionFind<K> for UnionFindWrapper<K> {
    // This is hacky, interface should be &K but I want runtime above all
    fn union(&mut self, key1: K, key2: K) -> (K, K) {
        if !self.trns.contains_left(&key1) {
            self.insert(key1);
        }
        if !self.trns.contains_left(&key2) {
            self.insert(key2);
        }
        let mut idx1 = unsafe { *self.trns.get_by_left(&key1).unwrap_unchecked() };
        let mut idx2 = unsafe { *self.trns.get_by_left(&key2).unwrap_unchecked() };
        // I need to union by the keys of trns
        let mut k1 = self.uf.find_mut(idx1.into());
        let mut k2 = self.uf.find_mut(idx2.into());
        if self.trns.get_by_right(&(k1.0 as usize)) > self.trns.get_by_right(&(k2.0 as usize)) {
            std::mem::swap(&mut k1, &mut k2);
            std::mem::swap(&mut idx1, &mut idx2);
        }
        let (root1, root2) = self.uf.union_no_swap(k1, k2);
        let key1 = self.trns.get_by_right(&(root1.0 as usize)).unwrap();
        let key2 = self.trns.get_by_right(&(root2.0 as usize)).unwrap();
        (key1.clone(), key2.clone())
    }

    fn find(&self, key: K) -> K {
        let idx = self.trns.get_by_left(&key);
        match idx {
            None => return key,
            Some(idx) => {
                let root = self.uf.find((*idx).into());
                *self.trns.get_by_right(&(root.0 as usize)).unwrap()
            }
        }
    }

    fn len(&self) -> usize {
        self.trns.len()
    }
    
    fn clone_box(&self) -> Box<dyn UnionFind<K>> {
        Box::new(self.clone())
    }
    
    fn iter(&self) -> Box<dyn Iterator<Item = K> + '_> {
        Box::new(self.trns.iter().map(|(k, _)| *k))
    }
}

impl<K: Copy + Ord + Debug + Send + Sync + 'static> MutUnionFind<K> for UnionFindWrapper<K> {
    fn find_mut(&mut self, key: K) -> K {
        let idx = self.trns.get_by_left(&key);
        match idx {
            None => return key,
            Some(idx) => {
                let root = self.uf.find_mut((*idx).into());
                *self.trns.get_by_right(&(root.0 as usize)).unwrap()
            }
        }
    }
}

impl<K: Copy + Ord + Debug + Send + Sync + 'static> UnionFindWrapper<K> {
    pub fn insert(&mut self, key: K) {
        if self.trns.contains_left(&key) {
            return;
        }
        let id = self.uf.make_set();
        self.trns.insert(key, id.0 as usize);
    }

    /// Remove a node from the union-find. It will not remove the group, but it will remove a single node.
    /// Fails if the node is a leader.
    pub fn remove(&mut self, t: &K) -> Option<()> {
        let leader = self.find_mut(*t);
        if &leader == t {
            return None;
        }
        self.trns.remove_by_left(t);
        Some(())
    }

    pub fn contains(&self, key: &K) -> bool {
        self.trns.contains_left(key)
    }
}

impl<K: Copy + Ord + Debug> UnionFindWrapper<K> {
    #[allow(dead_code)]
    pub(crate) fn debug_print_all(&self) {
        for (k, v) in self.trns.iter() {
            println!("{:?}: {:?}", k, v);
        }
        for p in &self.uf.parents {
            println!("{:?}", p);
        }
    }
}


#[cfg(test)]
mod tests {
    use crate::unionfind::SimpleUnionFind;
    use super::*;

    fn ids(us: impl IntoIterator<Item = usize>) -> Vec<Id> {
        us.into_iter().map(|u| u.into()).collect()
    }

    #[test]
    fn union_find() {
        let n = 10;
        let id = Id::from;

        let mut uf = SimpleUnionFind::default();
        for _ in 0..n {
            uf.make_set();
        }

        // test the initial condition of everyone in their own set
        assert_eq!(uf.parents, ids(0..n));

        // build up one set
        uf.union(id(0), id(1));
        uf.union(id(0), id(2));
        uf.union(id(0), id(3));

        // build up another set
        uf.union(id(6), id(7));
        uf.union(id(6), id(8));
        uf.union(id(6), id(9));

        // this should compress all paths
        for i in 0..n {
            uf.find_mut(id(i));
        }

        // indexes:         0, 1, 2, 3, 4, 5, 6, 7, 8, 9
        let expected = vec![0, 0, 0, 0, 4, 5, 6, 6, 6, 6];
        assert_eq!(uf.parents, ids(expected));
    }
}
