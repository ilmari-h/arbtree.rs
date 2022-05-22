//! # arbtree
//!
//! `arbtree` is a library for general purpose tree data structures.
//!
//! The library provides an interface for working with trees of arbitrary depth and width.
//! The implementation is simple and uses arena allocation where nodes are stored in a `Vec`.
//! No unsafe blocks and no additional overhead from using smart pointers.
//!
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Display;
use std::ops::Index;

#[derive(Debug, PartialEq, Clone)]
pub struct Node<T> {
    pub val: T,
    pub pos: NodePosition,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NodePosition {
    pub depth: usize,
    pub arena_idx: usize,
    pub children: Vec<usize>,
    pub parent_idx: usize,
}

pub struct Tree<T> {
    nodes: Vec<Node<T>>,
}

impl<T> Display for Tree<T>
where
    T: PartialEq + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut unclosed: HashSet<usize> = HashSet::new();
        let result: (String, HashMap<usize, Vec<usize>>) = self.nodes_dfs().fold(
            ("".to_string(), HashMap::new()),
            |(mut acc, mut siblings), node| {
                let depth = node.pos.depth;
                let mut is_last = false;
                if let Some(last) = siblings.get(&node.pos.parent_idx).and_then(|v| v.last()) {
                    if *last != node.pos.arena_idx {
                        unclosed.insert(depth);
                    } else {
                        is_last = true;
                        unclosed.remove(&depth);
                    }
                }

                let columns: String = (0..depth)
                    .map(|depth| {
                        if unclosed.contains(&depth) {
                            "│"
                        } else {
                            " "
                        }
                    })
                    .collect();
                let branch = if node.pos.depth == 0 {
                    "─"
                } else if is_last {
                    "└"
                } else {
                    "├"
                };

                acc = acc
                    + &format!(
                        "{}{}{}",
                        columns,
                        branch,
                        if node.pos.children.len() > 0 {
                            "┬"
                        } else {
                            "─"
                        }
                    )
                    .to_string()
                    + &format!("─ {}\n", node.val).to_string();

                siblings.insert(node.pos.arena_idx, node.pos.children.clone());

                (acc, siblings)
            },
        );
        write!(f, "{}", result.0)
    }
}

pub struct TreeIter<'a, T> {
    dfs: bool,
    idx_queue: VecDeque<usize>,
    arena: Vec<&'a Node<T>>,
}

impl<'a, T> Iterator for TreeIter<'a, T> {
    type Item = &'a Node<T>;
    fn next(&mut self) -> Option<Self::Item> {
        let n_i = self.idx_queue.pop_front()?;
        if n_i > self.arena.len() - 1 {
            return None;
        }
        let found = &self.arena[n_i];
        if self.dfs {
            for leaf_idx in found.pos.children.iter().rev() {
                self.idx_queue.push_front(*leaf_idx)
            }
        } else {
            self.idx_queue.extend(&found.pos.children);
        }
        return Some(&self.arena[n_i]);
    }
}

impl<T> ExactSizeIterator for TreeIter<'_,T> {
    fn len(&self) -> usize {
        self.arena.len()
    }
}

impl<T> Index<usize> for Tree<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        return &self.get(index).unwrap();
    }
}

pub trait ComprTree<T>
where
    T: PartialEq,
{
    fn find_mut_node(&mut self, comp: &T) -> Option<&mut Node<T>>;
    fn find_node(&self, comp: &T) -> Option<&Node<T>>;
    fn add_node(&mut self, parent: &T, val: T) -> Option<NodePosition>;
}

impl<T> ComprTree<T> for Tree<T>
where
    T: PartialEq,
{
    fn find_mut_node(&mut self, comp: &T) -> Option<&mut Node<T>> {
        return self.nodes.iter_mut().find(|n| &n.val == comp);
    }

    fn find_node(&self, comp: &T) -> Option<&Node<T>> {
        return self.nodes.iter().find(|n| &n.val == comp);
    }

    fn add_node(&mut self, parent: &T, val: T) -> Option<NodePosition> {
        let n_i = self.nodes.len();
        let parent = self.find_mut_node(parent)?;
        let p_depth = parent.pos.depth;
        let p_idx = parent.pos.arena_idx;
        parent.pos.children.push(n_i);
        let pos: NodePosition = NodePosition {
            depth: p_depth + 1,
            arena_idx: n_i,
            parent_idx: p_idx,
            children: Vec::new(),
        };
        self.nodes.push(Node {
            val,
            pos: pos.clone(),
        });
        return Some(pos);
    }
}

impl<T> Tree<T> {
    pub fn new(root: T) -> Self {
        let pos: NodePosition = NodePosition {
            depth: 0,
            arena_idx: 0,
            parent_idx: usize::MAX,
            children: Vec::new(),
        };
        return Self {
            nodes: vec![Node { val: root, pos }],
        };
    }

    pub fn nodes_bfs(&self) -> TreeIter<'_, T> {
        let references: Vec<&Node<T>> = self.nodes.iter().map(|owned| owned).collect();
        return TreeIter {
            dfs: false,
            idx_queue: VecDeque::from([0]),
            arena: references,
        };
    }

    pub fn nodes_dfs(&self) -> TreeIter<'_, T> {
        let references: Vec<&Node<T>> = self.nodes.iter().map(|owned| owned).collect();
        return TreeIter {
            dfs: true,
            idx_queue: VecDeque::from([0]),
            arena: references,
        };
    }

    pub fn get_node(&self, index: usize) -> Option<&Node<T>> {
        self.nodes.get(index)
    }

    pub fn get_mut_node(&mut self, index: usize) -> Option<&mut Node<T>> {
        self.nodes.get_mut(index)
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        return self.get_node(index).map(|x| &x.val);
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        return self.get_mut_node(index).map(|x| &mut x.val);
    }

    pub fn add_child_to_index(&mut self, parent_index: usize, val: T) -> Option<NodePosition> {
        let n_i = self.nodes.len();
        let parent = self.get_mut_node(parent_index)?;
        let p_depth = parent.pos.depth;
        let p_idx = parent.pos.arena_idx;
        parent.pos.children.push(n_i);
        let pos: NodePosition = NodePosition {
            depth: p_depth + 1,
            arena_idx: n_i,
            parent_idx: p_idx,
            children: Vec::new(),
        };
        self.nodes.push(Node {
            val,
            pos: pos.clone(),
        });
        return Some(pos);
    }

    /**
     * Place a node to the position of another node, pointed to by index. Pushes siblings to right.
     * Fails if no node found at index or if node at index is the root.
     */
    pub fn emplace(&mut self, index: usize, val: T) -> Option<NodePosition> {
        let new_index = self.nodes.len();
        let valid_index = new_index > index && index != 0;
        if !valid_index {
            return None;
        };

        let p_idx = self.get_node(index).map(|n| n.pos.parent_idx)?;
        let parent = self.get_node(p_idx)?;
        let idx = parent.pos.arena_idx;
        let d = parent.pos.depth;
        let new_pos = NodePosition {
            depth: d + 1,
            children: vec![],
            arena_idx: new_index,
            parent_idx: idx,
        };
        let new_node = Node {
            val,
            pos: new_pos.clone(),
        };
        self.nodes.push(new_node);
        let mut_parent = self.get_mut_node(p_idx).unwrap();
        let emplace_child_idx = mut_parent
            .pos
            .children
            .iter()
            .position(|n| *n == index)
            .unwrap();
        mut_parent.pos.children.insert(emplace_child_idx, new_index);
        return Some(new_pos);
    }
}

#[cfg(test)]
mod tree_t {
    use super::*;

    fn make_tree() -> Tree<&'static str> {
        let mut tree: Tree<&str> = Tree::new("a"); // 0
        tree.add_node(&"a", "b"); // 1
        tree.add_node(&"a", "c"); // 2
        tree.add_node(&"a", "d"); // 3
        tree.add_node(&"b", "e"); // 4
        tree.add_node(&"c", "f"); // 5
        tree.add_node(&"c", "g"); // 6
        return tree;
    }

    #[test]
    fn initialization() {
        let tree: Tree<&str> = make_tree();
        let vals = ["a", "b", "c", "d", "e", "f", "g"];

        assert_eq!(tree.nodes.len(), 7);

        let tree_values_in_order: Vec<&str> =
            (0..7).map(|index| *tree.get(index).unwrap()).collect();
        assert_eq!(tree_values_in_order, vals);
    }

    #[test]
    fn bfs_iteration() {
        let tree: Tree<&str> = make_tree();
        let vals = ["a", "b", "c", "d", "e", "f", "g"];
        assert!(tree.nodes_bfs().map(|n| n.val).eq(vals));
    }

    #[test]
    fn dfs_iteration() {
        let tree: Tree<&str> = make_tree();
        let vals = ["a", "b", "e", "c", "f", "g", "d"];
        assert!(tree.nodes_dfs().map(|n| n.val).eq(vals));
    }

    #[test]
    fn mutate_by_index() {
        let mut tree: Tree<&str> = make_tree();

        let mut new_child = tree.emplace(2, &"x").unwrap();
        assert_eq!(tree.get(new_child.arena_idx).unwrap(), &"x");
        new_child = tree.emplace(5, &"y").unwrap();
        assert_eq!(tree.get(new_child.arena_idx).unwrap(), &"y");

        let vals = ["a", "b", "x", "c", "d", "e", "y", "f", "g"];
        assert!(tree.nodes_bfs().map(|n| n.val).eq(vals));
    }
}
