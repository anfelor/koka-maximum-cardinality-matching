module matching

import graph

public alias matching = matching_
private struct matching_ {
    match_ : vector<node-id>
}

public fun new-matching(num_nodes : int) : matching {
    Matching_(vector(num_nodes, invalid-node-id))
}

public fun matched-to(m : matching, n : node-id) : <exn> int {
    m.match_[n]
}

public fun unmatch(m : matching, n : node-id) : <exn> matching {
    var v := m.match_
    if(v[n] != invalid-node-id) {
        v[v[n]] := invalid-node-id
    }
    v[n] := invalid-node-id
    Matching_(v)
}

public fun match-to(m' : matching, n : node-id, o : node-id) : <exn> matching {
    var m := m'
    m := m.unmatch(n)
    m := m.unmatch(o)
    var v := m.match_
    v[n] := o
    v[o] := n
    Matching_(v)
}

public fun num-nodes(m : matching) : int {
    return m.match_.length
}

public fun cardinality(m : matching) : int {
    var card := 0
    foreach(m.match_) fn(c) {
        if(c != invalid-node-id) card := card + 1
    }
    card / 2
}

public fun find-exposed(m : matching, to_ignore : vector<bool>) : <exn> node-id {
    for-while(0, m.num-nodes() - 1) fn(n) {
        if(m.match_[n] == invalid-node-id && !(to_ignore[n])) {
            Just(n)
        } else {
            Nothing
        }
    }.maybe(invalid-node-id)
}

// TODO: The compiler demands div, but why?
public fun to-graph(m : matching) : <exn, div> graph {
    var g := new-graph(m.num-nodes)
    for(0, m.num-nodes - 1) fn(x) {
        val y = m.matched-to(x)
        if(y != invalid-node-id && x < y) {
            g := g.add-edge(x, y)
        }
    }
    g
}
