module matching

import graph

public alias matching<h> = matching_<h>
private struct matching_<h> {
    match_ : ref<h, vector<node-id>>
}

public fun new-matching(num_nodes : int) : alloc<h> matching<h> {
    Matching_(ref(vector(num_nodes, invalid-node-id)))
}

public fun matched-to(m : matching<h>, n : node-id) : <exn, read<h>> int {
    (!m.match_)[n]
}

public fun unmatch(m : matching<h>, n : node-id) : <exn, st<h>> () {
    var v := !m.match_
    if(v[n] != invalid-node-id) {
        v[v[n]] := invalid-node-id
    }
    v[n] := invalid-node-id
    m.match_.set(v)
}

public fun match-to(m : matching<h>, n : node-id, o : node-id) : <exn, st<h>> () {
    m.unmatch(n)
    m.unmatch(o)
    var v := !m.match_
    v[n] := o
    v[o] := n
    m.match_.set(v)
}

public fun num-nodes(m : matching<h>) : <read<h>> int {
    return (!m.match_).length
}

public fun cardinality(m : matching<h>) : <read<h>> int {
    var card := 0
    foreach(!m.match_) fn(c) {
        if(c != invalid-node-id) card := card + 1
    }
    card / 2
}

public fun find-exposed(m : matching<h>, to_ignore : vector<bool>) : <exn, st<h>> node-id {
    for-while(0, m.num-nodes() - 1) fn(n) {
        if((!m.match_)[n] == invalid-node-id && !(to_ignore[n])) {
            Just(n)
        } else {
            Nothing
        }
    }.maybe(invalid-node-id)
}

// TODO: The compiler demands div, but why?
public fun to-graph(m : matching<h>) : <st<h>, exn, div> graph<h> {
    var g := new-graph(m.num-nodes)
    for(0, m.num-nodes - 1) fn(x) {
        val y = m.matched-to(x)
        if(y != invalid-node-id && x < y) {
            g.add-edge(x, y)
        }
    }
    g
}
