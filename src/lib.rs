//! # Arena based tree data structure
//!
//! This is a fork of the [`indextree` crate](https://github.com/saschagrunert/indextree) 
//! which allows to remove nodes. The original version was not capable of removing
//! nodes as the initial idea was to drop all nodes at the same time if the lifetime 
//! of the underlying memory arena has ended.
//! 
//! The arena tree structure is using a single `Vec`, a `HashMap` and numerical 
//! identifiers. Every node holds an id which is mapped to an index of the vector
//! via the `HashMap`. This allows to drop single nodes before the lifetime of the
//! arena hash ended. The downside is that this disables the general multiprocessing 
//! support of the original approach as `HashMap`s are not thread safe itself.
//! 
//! There is no `RefCell` and mutability is handled in a way much more idiomatic to Rust 
//! through unique (&mut) access to the arena. 
//!
//! # Example usage
//! ```
//! use indextree_ng::Arena;
//!
//! // Create a new arena
//! let arena = &mut Arena::new();
//!
//! // Add some new nodes to the arena
//! let a = arena.new_node(1);
//! let b = arena.new_node(2);
//!
//! // Append b to a
//! a.append(b, arena);
//! assert_eq!(b.ancestors(arena).into_iter().count(), 2);
//!
//! //Access a node
//! assert_eq!(arena[b].data, 2);
//!
//! // Remove a node
//! arena.remove_node(a);
//! assert_eq!(b.ancestors(arena).into_iter().count(), 1);
//!
//! ```
use std::{mem, fmt};
use std::error;
use std::collections::HashMap;
use std::ops::{Index, IndexMut};

pub use self::IndexTreeError::*;

#[doc = "
Use this for catching errors that
can happen when using indextree_ng::Tree.
"]
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum IndexTreeError {
    /// Tried to apply a method to the same node like node.append(node, arena)
    SameNodeErr,
}

impl fmt::Display for IndexTreeError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(error::Error::description(self))
    }
}

impl error::Error for IndexTreeError {
    fn description(&self) -> &str {
        match *self {
            SameNodeErr => "Tried to apply a method to the same node like node.append(node, arena)",
        }
    }
}


#[derive(PartialEq, Eq, Copy, Clone, Debug)]
/// A node identifier within a particular `Arena`
pub struct NodeId {
    id: usize,
}

#[derive(Clone, Debug)]
/// A node within a particular `Arena`
pub struct Node<T> {
    // Keep these private (with read-only accessors) so that we can keep them consistent.
    // E.g. the parent of a node’s child is that node.
    parent: Option<NodeId>,
    previous_sibling: Option<NodeId>,
    next_sibling: Option<NodeId>,
    first_child: Option<NodeId>,
    last_child: Option<NodeId>,

    /// The actual data which will be stored within the tree
    pub data: T,
}

impl<T> fmt::Display for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parent: {:?}, ", self.parent)?;
        write!(f, "Previous sibling: {:?}, ", self.previous_sibling)?;
        write!(f, "Next sibling: {:?}, ", self.next_sibling)?;
        write!(f, "First child: {:?}, ", self.first_child)?;
        write!(f, "Last child: {:?}", self.last_child)
    }
}

#[derive(Clone, Debug)]
/// An `Arena` structure containing certain Nodes
pub struct Arena<T> {
    nodes: Vec<Node<T>>,
    lookup: HashMap<usize, usize>,
}

impl<T> Arena<T> {
    /// Create a new empty `Arena`
    pub fn new() -> Arena<T> {
        Arena { nodes: Vec::new(),
                lookup: HashMap::new(), }
    }

    /// Create a new node from its associated data.
    pub fn new_node(&mut self, data: T) -> NodeId {
        let next_index = self.nodes.len();
        let next_id = self.lookup.keys().fold(0, |acc, &x| std::cmp::max(acc+1, x));
        self.nodes.push(Node {
            parent: None,
            first_child: None,
            last_child: None,
            previous_sibling: None,
            next_sibling: None,
            data: data,
        });
        self.lookup.insert(next_id, next_index);
        NodeId { id: next_id }
    }

    /// Removes a node from the arena. Detaches all children before.
    pub fn remove_node(&mut self, node: NodeId) {
        let index = *self.lookup.get(&node.id).expect("No node for given NodeId");

        let mut children: Vec<NodeId> = vec![];
        for child in node.children(self) {
            children.push(child.clone());
        }
        for child in children {
            child.detach(self);
        }

        let highest_index = self.nodes.len() - 1;
        let mut highest_index_id: usize = 0;
        for (key, value)  in self.lookup.iter() {
            if *value == highest_index {
                highest_index_id = *key;
                break;
            }
        }

        let _ = self.lookup.remove(&node.id);
        let _ = self.nodes.swap_remove(index);
        self.lookup.insert(highest_index_id, index);
    }
    
    /// Returns the number of nodes in Arena
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    
    /// Returns true if arena has no nodes, false otherwise
    pub fn is_empty(&self) -> bool {
        if self.len() == 0 {
            true
        }
        else {
            false
        }
    }

    // Get mutable references to two distinct nodes. Returns IndexTreeError::SameNodeErr if a == b.
    fn get_pair_mut(&mut self, a: &NodeId, b: &NodeId) -> Result<(&mut Node<T>, &mut Node<T>), IndexTreeError> {
        if a.id == b.id {
            return Err(IndexTreeError::SameNodeErr);
        }

        let error_msg = "No node for NodeId";
        let a_index = *self.lookup.get(&a.id).expect(error_msg);
        let b_index = *self.lookup.get(&b.id).expect(error_msg);
        
        let (xs, ys) = self.nodes.split_at_mut(std::cmp::max(a_index, b_index));
        if a_index < b_index {
            Ok((&mut xs[a_index], &mut ys[0]))
        } else {
            Ok((&mut ys[0], &mut xs[b_index]))
        }
    }
}

impl<T> Index<NodeId> for Arena<T> {
    type Output = Node<T>;

    fn index(&self, node: NodeId) -> &Node<T> {
        let node_index = *self.lookup.get(&node.id).expect("No node for this NodeId");
        &self.nodes[node_index]
    }
}

impl<T> IndexMut<NodeId> for Arena<T> {
    fn index_mut(&mut self, node: NodeId) -> &mut Node<T> {
        let node_index = *self.lookup.get(&node.id).expect("No node for this NodeId");
        &mut self.nodes[node_index]
    }
}

impl<T> Node<T> {
    /// Return the ID of the parent node, unless this node is the root of the tree.
    pub fn parent(&self) -> Option<NodeId> {
        self.parent
    }

    /// Return the ID of the first child of this node, unless it has no child.
    pub fn first_child(&self) -> Option<NodeId> {
        self.first_child
    }

    /// Return the ID of the last child of this node, unless it has no child.
    pub fn last_child(&self) -> Option<NodeId> {
        self.last_child
    }

    /// Return the ID of the previous sibling of this node, unless it is a first child.
    pub fn previous_sibling(&self) -> Option<NodeId> {
        self.previous_sibling
    }

    /// Return the ID of the previous sibling of this node, unless it is a first child.
    pub fn next_sibling(&self) -> Option<NodeId> {
        self.next_sibling
    }
}

impl NodeId {
    /// Return an iterator of references to this node and its ancestors.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn ancestors<T>(self, arena: &Arena<T>) -> Ancestors<T> {
        Ancestors {
            arena: arena,
            node: Some(self),
        }
    }

    /// Return an iterator of references to this node and the siblings before it.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn preceding_siblings<T>(self, arena: &Arena<T>) -> PrecedingSiblings<T> {
        PrecedingSiblings {
            arena: arena,
            node: Some(self),
        }
    }

    /// Return an iterator of references to this node and the siblings after it.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn following_siblings<T>(self, arena: &Arena<T>) -> FollowingSiblings<T> {
        FollowingSiblings {
            arena: arena,
            node: Some(self),
        }
    }

    /// Return an iterator of references to this node’s children.
    pub fn children<T>(self, arena: &Arena<T>) -> Children<T> {
        Children {
            arena: arena,
            node: arena[self].first_child,
        }
    }

    /// Return an iterator of references to this node’s children, in reverse order.
    pub fn reverse_children<T>(self, arena: &Arena<T>) -> ReverseChildren<T> {
        ReverseChildren {
            arena: arena,
            node: arena[self].last_child,
        }
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    ///
    /// Parent nodes appear before the descendants.
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn descendants<T>(self, arena: &Arena<T>) -> Descendants<T> {
        Descendants(self.traverse(arena))
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    pub fn traverse<T>(self, arena: &Arena<T>) -> Traverse<T> {
        Traverse {
            arena: arena,
            root: self,
            next: Some(NodeEdge::Start(self)),
        }
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    pub fn reverse_traverse<T>(self, arena: &Arena<T>) -> ReverseTraverse<T> {
        ReverseTraverse {
            arena: arena,
            root: self,
            next: Some(NodeEdge::End(self)),
        }
    }

    /// Detach a node from its parent and siblings. Children are not affected.
    pub fn detach<T>(self, arena: &mut Arena<T>) {
        let (parent, previous_sibling, next_sibling) = {
            let node = &mut arena[self];
            (node.parent.take(), node.previous_sibling.take(), node.next_sibling.take())
        };

        if let Some(next_sibling) = next_sibling {
            arena[next_sibling].previous_sibling = previous_sibling;
        } else if let Some(parent) = parent {
            arena[parent].last_child = previous_sibling;
        }

        if let Some(previous_sibling) = previous_sibling {
            arena[previous_sibling].next_sibling = next_sibling;
        } else if let Some(parent) = parent {
            arena[parent].first_child = next_sibling;
        }
    }

    /// Append a new child to this node, after existing children.
    pub fn append<T>(self, new_child: NodeId, arena: &mut Arena<T>) -> Result<(), IndexTreeError> {
        new_child.detach(arena);
        let last_child_opt;
        {
            let (self_borrow , new_child_borrow) = arena.get_pair_mut(&self,
                                                                      &new_child)?;
            new_child_borrow.parent = Some(self);
            last_child_opt = mem::replace(&mut self_borrow.last_child, Some(new_child));
            if let Some(last_child) = last_child_opt {
                new_child_borrow.previous_sibling = Some(last_child);
            } else {
                debug_assert!(self_borrow.first_child.is_none());
                self_borrow.first_child = Some(new_child);
            }
        }
        if let Some(last_child) = last_child_opt {
            debug_assert!(arena[last_child].next_sibling.is_none());
            arena[last_child].next_sibling = Some(new_child);
        }

        Ok(())
    }

    /// Prepend a new child to this node, before existing children.
    pub fn prepend<T>(self, new_child: NodeId, arena: &mut Arena<T>) -> Result<(), IndexTreeError> {
        new_child.detach(arena);
        let first_child_opt;
        {
            let (self_borrow, new_child_borrow) = arena.get_pair_mut(&self,
                                                                     &new_child)?;
        
            new_child_borrow.parent = Some(self);
            first_child_opt = mem::replace(&mut self_borrow.first_child, Some(new_child));
            if let Some(first_child) = first_child_opt {
                new_child_borrow.next_sibling = Some(first_child);
            } else {
                self_borrow.last_child = Some(new_child);
                debug_assert!(&self_borrow.first_child.is_none());
            }
        }
        if let Some(first_child) = first_child_opt {
            debug_assert!(arena[first_child].previous_sibling.is_none());
            arena[first_child].previous_sibling = Some(new_child);
        }

        Ok(())
    }

    /// Insert a new sibling after this node.
    pub fn insert_after<T>(self, new_sibling: NodeId, arena: &mut Arena<T>) -> Result<(), IndexTreeError> {
        new_sibling.detach(arena);
        let next_sibling_opt;
        let parent_opt;
        {
            let (self_borrow, new_sibling_borrow) = arena.get_pair_mut(&self,
                                                                      &new_sibling)?;
        
            parent_opt = self_borrow.parent;
            new_sibling_borrow.parent = parent_opt;
            new_sibling_borrow.previous_sibling = Some(self);
            next_sibling_opt = mem::replace(&mut self_borrow.next_sibling, Some(new_sibling));
            if let Some(next_sibling) = next_sibling_opt {
                new_sibling_borrow.next_sibling = Some(next_sibling);
            }
        }
        if let Some(next_sibling) = next_sibling_opt {
            debug_assert!(arena[next_sibling].previous_sibling.unwrap() == self);
            arena[next_sibling].previous_sibling = Some(new_sibling);
        } else if let Some(parent) = parent_opt {
            debug_assert!(arena[parent].last_child.unwrap() == self);
            arena[parent].last_child = Some(new_sibling);
        }

        Ok(())
    }

    /// Insert a new sibling before this node.
    pub fn insert_before<T>(self, new_sibling: NodeId, arena: &mut Arena<T>) -> Result<(), IndexTreeError> {
        new_sibling.detach(arena);
        let previous_sibling_opt;
        let parent_opt;
        {
            let (self_borrow, new_sibling_borrow) = arena.get_pair_mut(&self,
                                                                      &new_sibling)?;
            parent_opt = self_borrow.parent;
            new_sibling_borrow.parent = parent_opt;
            new_sibling_borrow.next_sibling = Some(self);
            previous_sibling_opt = mem::replace(&mut self_borrow.previous_sibling, Some(new_sibling));
            if let Some(previous_sibling) = previous_sibling_opt {
                new_sibling_borrow.previous_sibling = Some(previous_sibling);
            }
        }
        if let Some(previous_sibling) = previous_sibling_opt {
            debug_assert!(arena[previous_sibling].next_sibling.unwrap() == self);
            arena[previous_sibling].next_sibling = Some(new_sibling);
        } else if let Some(parent) = parent_opt {
            debug_assert!(arena[parent].first_child.unwrap() == self);
            arena[parent].first_child = Some(new_sibling);
        }

        Ok(())
    }
}

macro_rules! impl_node_iterator {
    ($name: ident, $next: expr) => {
        impl<'a, T> Iterator for $name<'a, T> {
            type Item = NodeId;

            fn next(&mut self) -> Option<NodeId> {
                match self.node.take() {
                    Some(node) => {
                        self.node = $next(&self.arena[node]);
                        Some(node)
                    }
                    None => None
                }
            }
        }
    }
}

/// An iterator of references to the ancestors a given node.
pub struct Ancestors<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(Ancestors, |node: &Node<T>| node.parent);

/// An iterator of references to the siblings before a given node.
pub struct PrecedingSiblings<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(PrecedingSiblings, |node: &Node<T>| node.previous_sibling);

/// An iterator of references to the siblings after a given node.
pub struct FollowingSiblings<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(FollowingSiblings, |node: &Node<T>| node.next_sibling);

/// An iterator of references to the children of a given node.
pub struct Children<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(Children, |node: &Node<T>| node.next_sibling);

/// An iterator of references to the children of a given node, in reverse order.
pub struct ReverseChildren<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(ReverseChildren, |node: &Node<T>| node.previous_sibling);

/// An iterator of references to a given node and its descendants, in tree order.
pub struct Descendants<'a, T: 'a>(Traverse<'a, T>);

impl<'a, T> Iterator for Descendants<'a, T> {
    type Item = NodeId;

    fn next(&mut self) -> Option<NodeId> {
        loop {
            match self.0.next() {
                Some(NodeEdge::Start(node)) => return Some(node),
                Some(NodeEdge::End(_)) => {}
                None => return None,
            }
        }
    }
}

#[derive(Debug, Clone)]
/// Indicator if the node is at a start or endpoint of the tree
pub enum NodeEdge<T> {
    /// Indicates that start of a node that has children. Yielded by `Traverse::next` before the
    /// node’s descendants. In HTML or XML, this corresponds to an opening tag like `<div>`
    Start(T),

    /// Indicates that end of a node that has children. Yielded by `Traverse::next` after the
    /// node’s descendants. In HTML or XML, this corresponds to a closing tag like `</div>`
    End(T),
}


/// An iterator of references to a given node and its descendants, in tree order.
pub struct Traverse<'a, T: 'a> {
    arena: &'a Arena<T>,
    root: NodeId,
    next: Option<NodeEdge<NodeId>>,
}

impl<'a, T> Iterator for Traverse<'a, T> {
    type Item = NodeEdge<NodeId>;

    fn next(&mut self) -> Option<NodeEdge<NodeId>> {
        match self.next.take() {
            Some(item) => {
                self.next = match item {
                    NodeEdge::Start(node) => {
                        match self.arena[node].first_child {
                            Some(first_child) => Some(NodeEdge::Start(first_child)),
                            None => Some(NodeEdge::End(node)),
                        }
                    }
                    NodeEdge::End(node) => {
                        if node == self.root {
                            None
                        } else {
                            match self.arena[node].next_sibling {
                                Some(next_sibling) => Some(NodeEdge::Start(next_sibling)),
                                None => {
                                    match self.arena[node].parent {
                                        Some(parent) => Some(NodeEdge::End(parent)),

                                        // `node.parent()` here can only be `None`
                                        // if the tree has been modified during iteration,
                                        // but silently stoping iteration
                                        // seems a more sensible behavior than panicking.
                                        None => None,
                                    }
                                }
                            }
                        }
                    }
                };
                Some(item)
            }
            None => None,
        }
    }
}

/// An iterator of references to a given node and its descendants, in reverse tree order.
pub struct ReverseTraverse<'a, T: 'a> {
    arena: &'a Arena<T>,
    root: NodeId,
    next: Option<NodeEdge<NodeId>>,
}

impl<'a, T> Iterator for ReverseTraverse<'a, T> {
    type Item = NodeEdge<NodeId>;

    fn next(&mut self) -> Option<NodeEdge<NodeId>> {
        match self.next.take() {
            Some(item) => {
                self.next = match item {
                    NodeEdge::End(node) => {
                        match self.arena[node].last_child {
                            Some(last_child) => Some(NodeEdge::End(last_child)),
                            None => Some(NodeEdge::Start(node)),
                        }
                    }
                    NodeEdge::Start(node) => {
                        if node == self.root {
                            None
                        } else {
                            match self.arena[node].previous_sibling {
                                Some(previous_sibling) => Some(NodeEdge::End(previous_sibling)),
                                None => {
                                    match self.arena[node].parent {
                                        Some(parent) => Some(NodeEdge::Start(parent)),

                                        // `node.parent()` here can only be `None`
                                        // if the tree has been modified during iteration,
                                        // but silently stoping iteration
                                        // seems a more sensible behavior than panicking.
                                        None => None,
                                    }
                                }
                            }
                        }
                    }
                };
                Some(item)
            }
            None => None,
        }
    }
}
