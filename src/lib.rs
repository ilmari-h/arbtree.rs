use std::{usize, collections::VecDeque, ops::Index, borrow::BorrowMut};


#[derive(Debug)]
struct Node<T> {
    val: T,
    children: Vec<usize>
}

struct Tree<T>
where T: PartialEq {
    nodes: Vec<Node<T>>
}

struct TreeIter<'a,T> {
    dfs: bool,
    idx_queue: VecDeque<usize>,
    arena: Vec<&'a Node<T>>
}

impl<'a,T> Iterator for TreeIter<'a,T> {
    type Item = &'a T;
    fn next(& mut self) -> Option<Self::Item> {
        if let Some(n_i) = self.idx_queue.pop_front() {
            if n_i > self.arena.len() - 1 { return None }
            let found = &self.arena[n_i];
            if self.dfs {
                for leaf_idx in found.children.iter().rev() {
                    self.idx_queue.push_front(*leaf_idx)
                }
            } else {
                self.idx_queue.extend(&found.children);
            }
            return Some(&self.arena[n_i].val);
        }
        return None;
    }
}

impl<T> Index<usize> for Tree<T>
where T: PartialEq{
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        return self.at(index).unwrap();
    }
}

impl<T> Tree<T>
where T: PartialEq {
    pub fn new(root: T) -> Self {
        return Self{nodes: vec![Node{val:root, children: Vec::new()}]};
    }

    pub fn iter_bfs(& self) -> TreeIter<'_,T> {
        let references: Vec<&Node<T>> = self.nodes.iter().map(|owned| owned).collect();
        return  TreeIter{dfs: false, idx_queue : VecDeque::from([0]), arena: references };
    }

    pub fn iter_dfs(& self) -> TreeIter<'_,T> {
        let references: Vec<&Node<T>> = self.nodes.iter().map(|owned| owned).collect();
        return  TreeIter{dfs: true, idx_queue : VecDeque::from([0]), arena: references };
    }

    pub fn at_mut(&mut self, index: usize) -> Option<&mut T> {
        let mut queue: VecDeque<usize> = VecDeque::from([0]);
        let mut i_count = 0;
        while let Some(n_i) = queue.pop_front() {
            if i_count > self.nodes.len() - 1 { return None }
            if i_count == index { return Some(&mut self.nodes[n_i].val)}
            let found = &self.nodes[n_i].children;
            queue.extend(found);
            i_count = i_count+1;
        }
        return None;
    }

    pub fn at(&self, index: usize) -> Option<&T> {
        let mut queue: VecDeque<usize> = VecDeque::from([0]);
        let mut i_count = 0;
        while let Some(n_i) = queue.pop_front() {
            if i_count > self.nodes.len() - 1 { return None }
            if i_count == index { return Some(&self.nodes[n_i].val)}
            let found = &self.nodes[n_i].children;
            queue.extend(found);
            i_count = i_count+1;
        }
        return None;
    }


    fn find_mut_node(&mut self, comp: &T) -> Option<&mut Node<T>> {
        let mut queue: VecDeque<usize> = VecDeque::from([0]);
        let mut i_count = 0;
        while let Some(n_i) = queue.pop_front() {
            if i_count > self.nodes.len() - 1 { return None }
            if &self.nodes[n_i].val == comp { return Some(&mut self.nodes[n_i])}
            let found = &self.nodes[n_i].children;
            queue.extend(found);
            i_count = i_count+1;
        }
        return None;
    }

    pub fn add_node(&mut self, parent: &T, val: T) -> Option<usize> {
        let n_i = self.nodes.len();
        if let Some(parent) = self.find_mut_node(parent) {
            parent.children.push(n_i);
            self.nodes.push(Node{val, children: Vec::new()});
            return Some(n_i);
        }
        return None;
    }
}

#[cfg(test)]
mod tests {
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
    fn tree_initialization() {
        let tree: Tree<&str> = make_tree();
        let vals = ["a","b","c","d","e","f","g"];

        assert_eq!(tree.nodes.len(), 7);

        let tree_values_in_order: Vec<&str> = (0..7).map(|index| *tree.at(index).unwrap()).collect();
        assert_eq!(tree_values_in_order, vals);
    }

    #[test]
    fn bfs_iteration() {
        let tree: Tree<&str> = make_tree();
        let vals = ["a","b","c","d","e","f","g"];
        let collected: Vec<&str> = tree.iter_bfs().map(|r| *r).collect();
        assert_eq!(collected, vals);
    }

    #[test]
    fn dfs_iteration() {
        let tree: Tree<&str> = make_tree();
        let vals = ["a","b","e","c","f","g","d"];
        let collected: Vec<&str> = tree.iter_dfs().map(|r| *r).collect();
        assert_eq!(collected, vals);
    }

    #[test]
    fn tree_mutation() {
        let mut tree: Tree<&str> = make_tree();
        let vals_bfs = ["a","b","c","d","e","f","g","h"];
        let vals_dfs = ["a","b","e","c","f","g","h","d"];
        tree.add_node(&"g", "h");
        let collected_bfs: Vec<&str> = tree.iter_bfs().map(|r| *r).collect();
        assert_eq!(collected_bfs, vals_bfs);

        let collected_dfs: Vec<&str> = tree.iter_dfs().map(|r| *r).collect();
        assert_eq!(collected_dfs, vals_dfs);
    }
}
