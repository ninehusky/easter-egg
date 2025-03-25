use crate::{egraph, SimpleUnionFind};
pub use crate::{Id, EGraph, Language, Analysis, ColorId};
use crate::{unionfind::UnionFind, Singleton};
use crate::util::JoinDisp;
use as_any::Downcast;
use invariants::dassert;
use itertools::Itertools;
use std::fmt::Formatter;
use indexmap::{IndexMap, IndexSet};
use crate::unionfind::UnionFindWrapper;

pub const BLACK_COLOR: ColorId = ColorId(0);

/// Represents an e-graph layer that implements its own congruence relation.
/// 
/// Each color represents a distinct congruence relation within the e-graph layers.
/// The ids in the union find are directly taken from its parent layer.
/// For efficiency, the color maintains the parent’s equality class for an id,
/// speeding up search and rebuild operations.
/// 
/// Currently, ids are not removed from the union find, which is wasteful but simpler.
/// An optimization could remove an id when it is merged in the parent, eliminating
/// redundancy; however, that would require updating all child colors to point to the new representative.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Color<L: Language, N: Analysis<L>> {
    color_id: ColorId,
    /// Used for rebuilding uf
    pub(crate) pending: Vec<Id>,
    /// Maintain which classes in black are represented in colored class (including rep)
    pub(crate) equality_classes: IndexMap<Id, IndexSet<Id>>,
    /// Used to implement a union find. Opposite function of `equality_classes`.
    /// Supports removal of elements when they are not needed.
    union_find: Box<dyn UnionFind<Id>>,
    /// Used to determine for each a colored equality class what is the black colored class.
    /// Relevant when a colored edge was added.
    pub(crate) children: Vec<ColorId>,
    pub(crate) parent: Option<ColorId>,
    parents: Vec<ColorId>,
    phantom: std::marker::PhantomData<(L, N)>,
}

impl<L: Language, N: Analysis<L>> Color<L, N> {
    pub(crate) fn collect_decendents(&self, egraph: &EGraph<L, N>) -> Vec<ColorId> {
        let mut res = self.children.clone();
        for c in self.children.iter() {
            res.extend(egraph.get_color(*c).unwrap().collect_decendents(egraph));
        }
        res
    }
}

impl<L: Language, N: Analysis<L>> Color<L, N> {
    pub(crate) fn new(new_id: ColorId, parent: Option<ColorId>, graph: &EGraph<L, N>) -> Color<L, N> {
        let parents = parent.map_or_else(|| vec![], |p| {
            let mut res = graph.get_color(p).unwrap().parents.clone();
            res.push(p);
            res
        });
        let union_find: Box<dyn UnionFind<Id>> = if parent.is_none() {
            // Box::new(SimpleUnionFind::default())
            // TODO: When remove optional color, this should go back to simple
            Box::new(UnionFindWrapper::default())
        } else {
            Box::new(UnionFindWrapper::default())
        };
        Color {
            color_id: new_id,
            pending: Default::default(),
            equality_classes: Default::default(),
            union_find,
            children: vec![],
            parent,
            parents,
            phantom: Default::default(),
        }
    }

    pub fn get_id(&self) -> ColorId {
        self.color_id
    }

    pub fn children(&self) -> &[ColorId] {
        &self.children
    }

    pub fn parents(&self) -> &[ColorId] {
        &self.parents
    }

    pub(crate) fn verify_uf_minimal(&self, egraph: &EGraph<L, N>) {
        let mut parents: IndexMap<Id, usize> = IndexMap::default();
        for k in self.union_find.iter() {
            let v = self.find(egraph, k);
            *parents.entry(v).or_default() += 1;
        }
        for (k, v) in parents {
            assert!(v >= 1, "Found {} parents for {}", v, k);
        }
    }

    pub fn find(&self, egraph: &EGraph<L, N>, id: Id) -> Id {
        let fixed = self.parent().map_or_else(|| egraph.find(id), |c_id| egraph.colored_find(c_id, id));
        self.union_find.find(fixed)
    }

    pub fn find_mut(&mut self, id: Id) -> Id {
        self.union_find.find_mut(id)
    }

    pub fn is_dirty(&self) -> bool { !self.pending.is_empty() }


    /// Update the color according to the union of base_to and base_from in the parent layer
    /// Assumes to and from canonised to the base (parent, black or colored) and !=
    /// @returns whether children need an update as well
    pub(crate) fn inner_base_union(&mut self, base_to: Id, base_from: Id) -> bool {
        // I should update the uf and the equality classes.
        // This should recursively try to update children until hitting a case they were both in UF and equal?
        //  1. If both were present but not equal I definitly need to union them, then I potentially need to remove from
        //  2. If both were present and equal I potentially need to remove from. This is a special case, no need to 
        //          recurse as any future child will see to and from as the same.
        //  3. Any of them was missing. I think if from was missing I need to change to new rep? Does it matter? 
        //          Not really, I just need to not assume I am holding parent rep
        dassert!(base_to != base_from, "Should not be the same");
        let uf: &mut UnionFindWrapper<Id> = self.union_find.as_mut().downcast_mut().unwrap();
        let from_existed = uf.contains(&base_from);
        let to_existed = uf.contains(&base_to);

        let diff = if to_existed && from_existed {
            // This part only needs to happen if one of the two is in the union find.
            let (colored_to, colored_from) =  self.inner_colored_union(base_to, base_from);
            self.equality_classes.entry(colored_to).and_modify(|s| { 
                s.swap_remove(&base_from); 
            });
            if self.equality_classes.get(&colored_to).map_or(false, |s| s.len() == 1) {
                dassert!(self.equality_classes.get(&colored_to).unwrap().contains(&colored_to), 
                    "We should always have the representative in the map");
                self.equality_classes.swap_remove(&colored_to);
            }
            colored_to != colored_from
        } else if from_existed {
            // If from existed, we need to update the to to be the new representative.
            let colored_from = self.find_mut(base_from);
            dassert!(base_to != colored_from, 
                    "Ids in colored union should not be the same if from existed and to didnt");
            let uf: &mut UnionFindWrapper<Id> = self.union_find.as_mut().downcast_mut().unwrap();
            uf.swap(base_from, base_to);
            self.equality_classes.entry(colored_from).and_modify(|s| { 
                s.swap_remove(&base_from); 
                s.insert(base_to);
            });
            self.pending.push(base_to);
            true
        } else {
            // TODO: I don't need to do anything here, right?
            let to = self.find_mut(base_to);
            dassert!(to != base_from, 
                "Ids in colored union should not be the same if to existed and from didnt");
            self.pending.push(to);
            true
        };

        diff
    }

    // Assumed id1 and id2 are parent canonized
    #[inline(always)]
    pub(crate) fn inner_colored_union(&mut self, id1: Id, id2: Id) -> (Id, Id) {
        // Parent classes will be updated in black union to come.
        let (to, from) = self.union_find.union(id1, id2);
        let changed = to != from;
        if changed {
            self.pending.push(to);
            let from_ids = self.equality_classes.swap_remove(&from).unwrap_or_else(|| IndexSet::singleton(from));
            self.equality_classes.entry(to).or_insert_with(|| IndexSet::singleton(to)).extend(from_ids);
        }
        (to, from)
    }

    pub fn base_equality_class(&self, egraph: &EGraph<L, N>, id: Id) -> Option<&IndexSet<Id>> {
        self.equality_classes.get(&self.find(egraph, id))
    }

    pub fn equality_class<'a>(&'a self, egraph: &'a EGraph<L, N>, id: Id) -> Box<dyn Iterator<Item = Id> + 'a> {
        let parent = self.parent();
        let fixed_id = self.find(egraph, id);
        let mut res: Box<dyn Iterator<Item = Id>> = if let Some(ids) = self.equality_classes.get(&fixed_id) {
            if let Some(c_id) = parent {
                Box::new(ids.into_iter().copied()
                    .flat_map(move |id| egraph.get_color(c_id).unwrap().equality_class(egraph, id)))
            } else {
                Box::new(ids.into_iter().copied())
            }
        } else {
            if let Some(c_id) = parent {
                Box::new(egraph.get_color(c_id).unwrap().equality_class(egraph, id))
            } else {
                Box::new(std::iter::once(id))
            }
        };
        dassert!({
            let temp = res.collect_vec();
            let r = temp.len() == temp.iter().unique().count();
            res = Box::new(temp.into_iter());
            r
        });
        res
    }

    /// Returns the black representative of the colored e-class of the current color only. Does not
    /// include the parents equality classes.
    pub fn current_black_reps(&self) -> impl Iterator<Item=&Id> {
        self.equality_classes.keys().into_iter()
    }

    pub fn parent(&self) -> Option<ColorId> { self.parent }

    pub fn get_all_enodes(&self, id: Id, egraph: &EGraph<L, N>) -> Vec<L> {
        let mut res: IndexSet<L> = IndexSet::default();
        for cls in self.equality_class(egraph, id) {
            res.extend(egraph[cls].nodes.iter().map(|n: &L| egraph.colored_canonize(self.color_id, n)));
        }
        return res.into_iter().collect_vec();
    }

    #[inline(always)]
    pub fn assert_black_ids(&self, egraph: &EGraph<L, N>) {
        // Check that black ids are actually black representatives
        dassert!({
            for (_, set) in &self.equality_classes {
                for id in set {
                    dassert!(egraph.find(*id) == *id, "black id {:?} is not black rep {:?}", id, egraph.find(*id));
                }
            }
            true
        });
    }
}

impl<L, N> std::fmt::Display for Color<L, N> where L: Language, N: Analysis<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Color(id={}, groups={})", self.color_id, self.equality_classes.iter().map(|(id, set)| format!("{} - {}", id, set.iter().sep_string(" "))).join(", "))
    }
}

#[cfg(test)]
mod test {

    // #[test]
    // fn test_black_union_alone() {
    //     let mut g = EGraph::<SymbolLang, ()>::new(());
    //     let id1 = g.add_expr(&"1".parse().unwrap());
    //     let id2 = g.add_expr(&"2".parse().unwrap());
    //     let mut color = Color::new(ColorId::from(0));
    //     color.black_union(&mut g, id1, id2);
    //     color.black_union(&mut g, id1, id2);
    //     color.black_union(&mut g, id1, id1);
    //     assert_eq!(color.find(&g, id1), color.find(&g, id2));
    // }
}
