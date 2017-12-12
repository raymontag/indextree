# indextree

[![Build Status](https://travis-ci.org/raymontag/indextree.svg?branch=master)](https://travis-ci.org/raymontag/indextree)

## Arena based tree structure with multithreading support
This is a fork of the [`indextree` crate](https://github.com/saschagrunert/indextree) 
which allows to remove nodes. The original version was not capable of removing
nodes as the initial idea was to drop all nodes at the same time if the lifetime 
of the underlying memory arena has ended.

The arena tree structure is using a single `Vec`, a `HashMap` and numerical 
identifiers. Every node holds an id which is mapped to an index of the vector
via the `HashMap`. This allows to drop single nodes before the lifetime of the
arena hash ended. The downside is that this disables the general multiprocessing 
support of the original approach as `HashMap`s are not thread safe itself.

There is no `RefCell` and mutability is handled in a way much more idiomatic to Rust 
through unique (&mut) access to the arena. 

### Example usage
```rust
use indextree::Arena;

// Create a new arena
let arena = &mut Arena::new();

// Add some new nodes to the arena
let a = arena.new_node(1);
let b = arena.new_node(2);

// Append b to a
a.append(b, arena);
assert_eq!(b.ancestors(arena).into_iter().count(), 2);

//Access a node
assert_eq!(arena[b], 2);

// Remove a node
arena.remove_node(a);
assert_eq!(b.ancestors(arena).into_iter().count(), 1);

```

