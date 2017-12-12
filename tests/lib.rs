extern crate indextree_ng;
use indextree_ng::Arena;

use std::cell::Cell;

struct DropTracker<'a>(&'a Cell<u32>);
impl<'a> Drop for DropTracker<'a> {
    fn drop(&mut self) {
        self.0.set(&self.0.get() + 1);
    }
}

#[test]
fn arenatree_success_create() {
    let drop_counter = Cell::new(0);
    {
        let mut new_counter = 0;
        let arena = &mut Arena::new();
        macro_rules! new {
            () => {{
                new_counter += 1;
                arena.new_node((new_counter, DropTracker(&drop_counter)))
            }}
        };

        let a = new!();  // 1
        assert!(a.append(new!(), arena).is_ok());  // 2
        assert!(a.append(new!(), arena).is_ok());  // 3
        assert!(a.prepend(new!(), arena).is_ok());  // 4
        let b = new!();  // 5
        assert!(b.append(a, arena).is_ok());
        assert!(a.insert_before(new!(), arena).is_ok());  // 6
        assert!(a.insert_before(new!(), arena).is_ok());  // 7
        assert!(a.insert_after(new!(), arena).is_ok());  // 8
        assert!(a.insert_after(new!(), arena).is_ok());  // 9
        let c = new!();  // 10
        assert!(b.append(c, arena).is_ok());

        assert_eq!(drop_counter.get(), 0);
        arena[c].previous_sibling().unwrap().detach(arena);
        assert_eq!(drop_counter.get(), 0);

        assert_eq!(b.descendants(arena).map(|node| arena[node].data.0).collect::<Vec<_>>(),
                   [5, 6, 7, 1, 4, 2, 3, 9, 10]);
    }

    assert_eq!(drop_counter.get(), 10);
}

#[test]
#[should_panic]
fn arenatree_failure_prepend() {
    let arena = &mut Arena::new();
    let a = arena.new_node(1);
    let b = arena.new_node(2);
    assert!(a.prepend(b, arena).is_ok());
}

#[test]
fn arenatree_success_detach() {
    let arena = &mut Arena::new();
    let a = arena.new_node(1);
    let b = arena.new_node(1);
    assert!(a.append(b, arena).is_ok());
    assert_eq!(b.ancestors(arena).into_iter().count(), 2);
    b.detach(arena);
    assert_eq!(b.ancestors(arena).into_iter().count(), 1);
}

#[test]
fn arenatree_remove_node() {
    let drop_counter = Cell::new(0);    
    let mut new_counter = 0;
    let arena = &mut Arena::new();
    macro_rules! new {
        () => {{
            new_counter += 1;
            arena.new_node((new_counter, DropTracker(&drop_counter)))
        }}
    };

    let a = new!();
    let b = new!();
    let c = new!();
    let d = new!();
    assert!(a.append(b, arena).is_ok());
    assert!(a.append(c, arena).is_ok());
    assert!(b.append(d, arena).is_ok());

    assert!(arena.remove_node(a).is_ok());
    assert_eq!(drop_counter.get(), 1);
    assert_eq!(arena.len(), 3);
    assert_eq!(b.ancestors(arena).into_iter().count(), 1);
    assert_eq!(c.ancestors(arena).into_iter().count(), 1);
    assert_eq!(d.ancestors(arena).into_iter().count(), 2);
}

