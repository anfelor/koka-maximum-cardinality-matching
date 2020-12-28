module components

import graph

public alias components<h> = components_<h>
private struct components_<h> {
    card_ : ref<h, vector<int>>
    id_ : ref<h, vector<node-id>>
}

public fun new-components(num_nodes : node-id) : <exn, alloc<h>> components<h> {
    var ids := vector(num_nodes, 0)
    for(0, num_nodes - 1) fn(i) {
        ids[i] := i
    }
    Components_(ref(vector(num_nodes, 1)), ref(ids))
}

// The combined cost of k calls to this function
// is O(nlog(n) + k), since the recursion can only
// happen more than once if x was in the smaller component during a merge
// (which can only happen log(n) times for each node).
public fun id(c : components<h>, x : node-id) : <exn, st<h>> node-id {
    var id' := !(c.id_)
    if(x != id'[x]) {
        id'[x] := c.id(unsafe-decreasing(id'[x]))
        c.id_.set(id')
    }
    id'[x]
}

public fun merge(c : components<h>, x : node-id, y : node-id) : <exn, st<h>> () {
    val x_ = c.id(x)
    val y_ = c.id(y)
    var id' := !(c.id_)
    var card' := !(c.card_)
    if(card'[x_] < card'[y_]) {
        id'[x_] := y_
        card'[y_] := card'[y_] + card'[x_]
    } else {
        id'[y_] := x_
        card'[x_] := card'[x_] + card'[y_]
    }
    c.id_.set(id')
    c.card_.set(card')
}