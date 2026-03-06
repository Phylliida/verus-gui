use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::node::Node;
use crate::padding::Padding;
use crate::layout::absolute::*;

verus! {

/// The output of absolute_children has length equal to (child_data.len() - index).
pub proof fn lemma_absolute_children_len<T: OrderedField>(
    padding: Padding<T>,
    child_data: Seq<(T, T, Size<T>)>,
    index: nat,
)
    requires
        index <= child_data.len(),
    ensures
        absolute_children(padding, child_data, index).len() == child_data.len() - index,
    decreases child_data.len() - index,
{
    if index >= child_data.len() {
        // base case: empty
    } else {
        lemma_absolute_children_len(padding, child_data, index + 1);
    }
}

/// Element access: absolute_children(padding, child_data, 0)[i] gives the node
/// at position (padding.left + x_i, padding.top + y_i) with the correct size.
pub proof fn lemma_absolute_children_element<T: OrderedField>(
    padding: Padding<T>,
    child_data: Seq<(T, T, Size<T>)>,
    i: nat,
)
    requires
        i < child_data.len(),
    ensures
        ({
            let children = absolute_children(padding, child_data, 0);
            let (x, y, sz) = child_data[i as int];
            &&& children.len() == child_data.len()
            &&& children[i as int].x == padding.left.add(x)
            &&& children[i as int].y == padding.top.add(y)
            &&& children[i as int].size == sz
            &&& children[i as int].children == Seq::<Node<T>>::empty()
        }),
    decreases i,
{
    lemma_absolute_children_len::<T>(padding, child_data, 0);
    if i == 0 {
        // Base: first element of push-add is the pushed element
    } else {
        // Inductive: element i of push-add is element i-1 of the tail
        lemma_absolute_children_len::<T>(padding, child_data, 1);
        lemma_absolute_children_shift::<T>(padding, child_data, 0, i);
    }
}

/// Helper: shifting the start index doesn't change element access when adjusted.
proof fn lemma_absolute_children_shift<T: OrderedField>(
    padding: Padding<T>,
    child_data: Seq<(T, T, Size<T>)>,
    start: nat,
    i: nat,
)
    requires
        start + i < child_data.len(),
        i > 0,
        absolute_children(padding, child_data, start).len() == child_data.len() - start,
    ensures
        ({
            let children = absolute_children(padding, child_data, start);
            let (x, y, sz) = child_data[(start + i) as int];
            &&& children[i as int].x == padding.left.add(x)
            &&& children[i as int].y == padding.top.add(y)
            &&& children[i as int].size == sz
            &&& children[i as int].children == Seq::<Node<T>>::empty()
        }),
    decreases i,
{
    lemma_absolute_children_len::<T>(padding, child_data, start + 1);
    // absolute_children(start) = push(node_at_start).add(absolute_children(start+1))
    // Element [0] is node_at_start, elements [1..] come from absolute_children(start+1)
    if i == 1 {
        // element [1] is element [0] of absolute_children(start+1)
        // which is the node at start+1
    } else {
        lemma_absolute_children_shift::<T>(padding, child_data, start + 1, (i - 1) as nat);
    }
}

} // verus!
