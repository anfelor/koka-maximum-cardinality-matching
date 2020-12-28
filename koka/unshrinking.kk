module unshrinking

import graph
import matching
import components

// Unlike in the presentation in the lecture, we don't actually
// shrink and unshrink. Instead we save the cycles and "unshrink"
// by finding an M-augmenting path in each cycle to align the
// near-perfect matching correctly.

// The first element is the apex (e.g. the node of the cycle
// highest up in the tree at the moment of creation).
// The second element are the edges. Since we use pseudo-nodes
// each node is given by the endpoint of its entering edges.
public struct cycle<h> {
    apex : (node-id, node-id)
    edges : ref<h, vector<edge>>
}

public fun show(c : cycle<h>) : <read<h>> string {
    var s := "Cycle((" + c.apex.fst.show + ", " + c.apex.snd.show + "), ["
    val edges = !c.edges
    edges.foreach fn(e){
        s := s + "(" + e.fst.show + ", " + e.snd.show + "), "
    }
    s + "]"
}

private fun reverse(c : vector<edge>) : <exn> vector<edge> {
    var c' := c
    for(0, c'.length() / 2) fn(i) {
        val j = c'.length() - 1 - i
        val tmp = c'[i]
        c'[i] := c'[j].invert
        c'[j] := tmp.invert
    }
    c'
}

public fun reverse(c : cycle<h>) : <st<h>, exn> cycle<h> {
    Cycle(c.apex, ref((!c.edges).reverse))
}

public alias unshrinking<h> = unshrinking_<h>
private struct unshrinking_<h> {
    cycles_ : list<cycle<h>>
    matched_cycle_ : ref<h, vector<int>>
}

public fun new-unshrinking(num_nodes : int) {
    Unshrinking_([], ref(vector(num_nodes, invalid-node-id)))
}

public fun add-cycle(u : unshrinking<h>, m : matching<h>, c : cycle<h>) : <exn, st<h>> unshrinking<h> {
    var e := !c.edges
    var mc_ := !u.matched_cycle_
    e.foreach fn(i) {
        if(m.matched-to(i.fst) == i.snd) {
            mc_[i.fst] := u.cycles_.length
            mc_[i.snd] := u.cycles_.length
        }
    }
    u.matched_cycle_.set(mc_)
    u(cycles_ = Cons(c, u.cycles_))
}

// Unshrink the matching cycle for a node R(x), where
// x has an incident matching edge into R(x).
public fun unshrink(u : unshrinking<h>, m : matching<h>, c : components<h>, x : node-id, expanded : list<int> = []) : <st<h>, exn, div> () {
    val y = m.matched-to(x)
    val comp = c.id(x)
    var mc_ := !u.matched_cycle_
    val mc = u.cycles_.length - mc_[x] - 1
    if(y == invalid-node-id) return ()
    if(c.id(y) != comp || (expanded.find fn(a){a == mc}).is-just) return ()
    var expanded' := Cons(mc, expanded)
    val cyc = u.cycles_[mc].unjust
    var cyce := !cyc.edges
    
    var next : int := for-while(0, cyce.length - 1) fn(i) {
        if(cyce[i].fst == x && cyce[i].snd == y) {
            return Just(i)
        }
        if(cyce[i].fst == y && cyce[i].snd == x) {
            cyce := reverse(cyce)
            return Just(cyce.length - i - 1)
        }
        Nothing
    }.unjust

    var match_next := False;
    while { (cyce[next].fst) != cyc.apex.fst && (cyce[next].fst) != cyc.apex.snd } {
        if(match_next) {
            if(mc_[cyce[next].fst] != mc_[x]) {
                u.unshrink(m, c, cyce[next].fst, expanded')
            }
            if(mc_[cyce[next].snd] != mc_[x]) {
                u.unshrink(m, c, cyce[next].snd, expanded')
            }
            m.match-to(cyce[next].fst, cyce[next].snd)
        }
        match_next := !match_next
        next := next + 1
        if(next == cyce.length) {
            next := 0
        }
    }
}