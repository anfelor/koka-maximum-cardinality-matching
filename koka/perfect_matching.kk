module perfect_matching

import graph
import matching
import components
import unshrinking

// A frustrated tree for a graph.
public struct frustrated-tree {
    root : node-id
    is-even : vector<bool>
    is-odd : vector<bool>
}

public fun until-just(pred : () -> <div|e> maybe<a>) : <div|e> a {
    match(pred()) {
        Just(a) -> a
        Nothing -> until-just(pred)
    }
}

private fun is-valid(e : edge) {
    e.fst != invalid-node-id && e.snd != invalid-node-id
}

// Find the path P between x and y in the tree given by pred \circ s.id
// in time O(|P|*log(|P|))
// TODO: The original implementation uses an additional set for 
// membership instead of just a list.
private fun find-cycle(pred : vector<edge>, s : components<h>, x : node-id, y : node-id) : <st<h>, exn, div> cycle {
    var from-x := Cons((x, x), Nil)
    var from-y := Cons((y, y), Nil)
    val undef = (x, x)
    fun comp(e : edge) { s.id(e.snd) }
    fun merge(fr : list<edge>, ba : list<edge>) {
        // TODO: this should be cleaner once list.find allows effects
        var fr' := Nil
        var quit-next := False
        fr.reverse.foreach-while fn(e) {
            if(quit-next) return Just(())
            quit-next := (e.comp == ba.head(undef).comp)
            fr' := Cons(e, fr')
            Nothing
        }
        val apex = (fr'.head(undef).snd, ba.head(undef).snd)
        val vec = fr'.reverse + ba.map fn(a){ (a.snd, a.fst) } 
        val vec' = match vec {
            Cons(h, t) -> Cons(if(h.fst == x) then (y, x) else (x, y), t.init)
            Nil -> Nil
        }
        Cycle(apex, vector(vec'))
    }
    until-just {
        if(from-x.any fn(a){ a.comp == from-y.head(undef).comp }) {
            return Just(merge(from-x, from-y))
        }
        if(from-y.any fn(a){ a.comp == from-x.head(undef).comp }) {
            return Just(merge(from-y, from-x))
        }
        val x' = pred[from-x.head(undef).comp]
        val y' = pred[from-y.head(undef).comp]
        if(x'.is-valid) {
            from-x := Cons(x', from-x)
        }
        if(y'.is-valid) {
            from-y := Cons(y', from-y)
        }
        Nothing
    }
}

private fun add-neighbors(l : list<edge>, g : graph, x : node-id, to-ignore : vector<bool>) : <st<h>, exn> list<edge> {
    var l' := l
    g.get-node(x).neighbors().foreach fn(y){
        if(! to-ignore[y]) {
            l' := Cons((x, y), l')
        }
    }
    l'
}

public fun perfect-matching(g : graph, m' : matching, to-ignore : vector<bool>) : <st<h>, exn, div> maybe<frustrated-tree> {
    var m := m'
    val r = m.find-exposed(to-ignore)
    if(r == invalid-node-id) {
        return Nothing
    }

    var c := new-components(g.num-nodes)
    var u := new-unshrinking(g.num-nodes)

    // A node in G is even if it is in a (node in G') in Even(T)
    var is-even := vector(g.num-nodes, False)
    is-even[r] := True

    // A node in G is odd if it is in Odd(T)
    var is-odd := vector(g.num-nodes, False)

    // The edge connecting to the predecessor in the tree.
    // Note that the first entry of the edge is the node from
    // which the current pseudo-node is left from.
    var pred := vector(g.num-nodes, invalid-edge)
    var l := Nil
    l := add-neighbors(l, g, r, to-ignore)
    var y := invalid-node-id

    until-just {
        match(l) {
            Nil -> return Just(Just(Frustrated-tree(r, is-even, is-odd)))
            Cons(e, l') -> {
                l := l'
                val x = e.fst
                y := e.snd
                if(! is-odd[y] && c.id(x) != c.id(y)) {
                    if(! is-even[y]) {
                        val z = m.matched-to(y)
                        pred[c.id(y)] := (y, x)
                        if(z == invalid-node-id) {
                            val old-card = m.cardinality
                            while { y != invalid-node-id } {
                                val e = pred[c.id(y)]
                                u.unshrink(m, c, e.snd)
                                m := m.match-to(e.fst, e.snd)
                                y := pred[c.id(e.snd)].snd
                            }
                            val new-card = m.cardinality
                            if(new-card != old-card + 1) {
                                throw-exn(Exception(new-card.show + " - " + old-card.show, ExnAssert))
                            }
                            return Just(perfect-matching(g, m, to-ignore))
                        } else {
                            is-odd[y] := True
                            is-even[z] := True
                            pred[c.id(z)] := (z, y)
                            l := add-neighbors(l, g, z, to-ignore)
                        }
                    } else {
                        val cycle = find-cycle(pred, c, x, y)
                        val apex-pred = pred[c.id(cycle.apex.fst)]
                        cycle.edges.foreach fn(i) {
                            if(is-odd[i.fst]) {
                                l := add-neighbors(l, g, i.fst, to-ignore)
                                is-even[i.fst] := True
                                is-odd[i.fst] := False
                            }
                            c.merge(i.fst, i.snd)
                        }
                        pred[c.id(cycle.apex.fst)] := apex-pred
                        u := u.add-cycle(m, cycle)
                        ()
                    }
                }
                Nothing
            }
        }
    }
}