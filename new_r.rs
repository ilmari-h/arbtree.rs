use std::collections::{VecDeque, HashSet, HashMap};
use std::borrow::ToOwned;
use std::fmt::Display;
use std::hash::Hash;

#[derive(Clone)]
pub struct Tree<T>{
    nodes: Vec<Node<T>>
}

#[derive(Debug)]
#[derive(Clone)]
pub struct Node<T> {
    pub val: T,
    pub pos: NodePosition
}

#[derive(Debug, Clone)]
pub struct NodePosition {
    pub depth: usize,
    pub siblings: usize,
    pub arena_idx: usize,
    pub children: Vec<usize>,
    pub parent_arena_idx: usize
}

impl<T> Display for Tree<T> where T: PartialEq + Display {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut unclosed: HashSet<usize> = HashSet::new();
        let result: (String,HashMap<usize, Vec<usize>>) = self
            .iter_dfs()
            .fold(("".to_string(),HashMap::new()),
                |(mut acc, mut siblings),node|
                {
                    let depth = node.pos.depth;
                    let mut is_last = false;
                    if let Some(last) = siblings.get(&node.pos.parent_arena_idx).and_then(|v| v.last()) {
                        if *last != node.pos.arena_idx {
                            unclosed.insert(depth);
                        }
                        else {
                            is_last = true;
                            unclosed.remove(&depth);
                        }
                    }

                    let columns: String = (0..depth).map(|depth| if unclosed.contains(&depth) {"│"} else {" "} ).collect();
                    let branch = if node.pos.depth == 0 {"─"} else if is_last {"└"} else {"├"} ;

                    acc =
                        acc +
                        &format!("{}{}{}",
                            columns,
                            branch,
                            if node.pos.children.len() > 0 {"┬"} else {"─"}
                        ).to_string() +
                        &format!("─ {}\n",node.val).to_string();

                    siblings.insert(node.pos.arena_idx, node.pos.children.clone());

                    (acc,siblings)
                }
            );
        write!(f,"{}",result.0)
    }
}

impl<T> Tree<T> {
    pub fn new(root: T) -> Self {
        let pos: NodePosition = NodePosition{
            depth: 0,
            siblings: 0,
            arena_idx: 0,
            parent_arena_idx: 0,
            children: Vec::new()
        };
        return Self{nodes: vec![Node{val:root, pos}]}
    }

    fn get_node_mut(&mut self, index: usize) -> Option<&mut Node<T>> {
        return self.nodes.get_mut(index);
    }

    fn get_node(&self, index: usize) -> Option<&Node<T>> {
        return self.nodes.get(index);
    }

//    fn remove_at(&mut self, index: usize) -> Result<(),()> {
//        if let None = self.nodes.get(index) {
//            return Err(());
//        }
//        let references: Vec<&Node<T>> = self.nodes
//            .iter()
//            .map(|owned| owned)
//            .collect();
//        let to_remove: Vec<usize> =
//            TreeIter{
//                idx_queue: VecDeque::from([index]),
//                arena: references, dfs: false
//            }
//            .map(|v| v.pos.arena_idx)
//            .collect();
//
//        println!("remove {:?}", to_remove);
//        // Remove in reverse order to not cause issues with shifting indices.
//        for remove_idx in to_remove.iter().rev() {
//            self.nodes.remove(*remove_idx);
//        }
//        return Ok(());
//    }

    pub fn iter_bfs(&self) -> TreeIter<'_,T> {
        let references: Vec<&Node<T>> = self.nodes.iter().map(|owned| owned).collect();
        return  TreeIter{idx_queue : VecDeque::from([0]), arena: references, dfs: false, size: self.nodes.len() };
    }
    pub fn iter_dfs(&self) -> TreeIter<'_,T> {
        let references: Vec<&Node<T>> = self.nodes.iter().map(|owned| owned).collect();
        return  TreeIter{idx_queue : VecDeque::from([0]), arena: references, dfs: true, size: self.nodes.len() };
    }

}

trait CompTree<T> where T: PartialEq {

    fn find_mut_node(&mut self, comp: &T) -> Option<&mut Node<T>>;
    fn find_node(&self, comp: &T) -> Option<&Node<T>>;
    fn add_node(&mut self, parent: &T, val: T) -> Option<NodePosition>;
}

impl<T> CompTree<T> for Tree<T> where T: PartialEq {

    fn find_node(&self, comp: &T) -> Option<&Node<T>> {
        return self.nodes.iter().find(|n| &n.val == comp);
    }

    fn find_mut_node(&mut self, comp: &T) -> Option<&mut Node<T>> {
        return self.nodes.iter_mut().find(|n| &n.val == comp);
    }

    fn add_node(&mut self, parent: &T, val: T) -> Option<NodePosition> {
        let n_i = self.nodes.len();
        if let Some(parent) = self.find_mut_node(parent) {
            parent.pos.children.push(n_i);
            let pos: NodePosition = NodePosition{
                depth: parent.pos.depth + 1,
                siblings: parent.pos.children.len() + 1,
                arena_idx: n_i,
                parent_arena_idx: parent.pos.arena_idx,
                children: Vec::new()
            };
            self.nodes.push(Node{val, pos: pos.clone()});
            return Some(pos);
        }
        return None;
    }
}

pub struct TreeIter<'a,T> {
    idx_queue: VecDeque<usize>,
    arena: Vec<&'a Node<T>>,
    dfs: bool,
    size: usize
}

impl<'a,T> Iterator for TreeIter<'a,T> {
    type Item = &'a Node<T>;
    fn next(& mut self) -> Option<Self::Item> {
        if let Some(n_i) = self.idx_queue.pop_front() {
            if n_i > self.arena.len() - 1 { return None }
            if let Some(found) = self.arena.get(n_i) {
                if self.dfs {
                    for leaf_idx in found.pos.children.iter().rev() {
                        self.idx_queue.push_front(*leaf_idx)
                    }
                } else {
                    self.idx_queue.extend(&found.pos.children);
                }
                return self.arena.get(n_i).map(|v| *v);
            }
        }
        return None;
    }
}

impl<T> ExactSizeIterator for TreeIter<'_,T> {
   fn len(&self) -> usize {
        self.size
    }
}

#[cfg(test)]
mod tree_t {
    use super::*;

    fn make_tree() -> Tree<&'static str> {
        let mut tree: Tree<&str> = Tree::new("a");
        tree.add_node(&"a", "b");
        tree.add_node(&"a", "c");
        tree.add_node(&"a", "d");
        tree.add_node(&"b", "e");
        tree.add_node(&"c", "f");
        tree.add_node(&"c", "g");
        return tree;
    }

    #[test]
    fn bfs_iteration() {
        let mut tree: Tree<&str> = make_tree();
        print!("{}",tree);
        assert_eq!( tree.iter_bfs().map(|r| r.val).collect::<Vec<_>>(), ["a","b","c","d","e","f","g"]);
        tree.add_node(&"b", "h");
        assert_eq!( tree.iter_bfs().map(|r| r.val).collect::<Vec<_>>(), ["a","b","c","d","e","h","f","g"]);
    }
}
