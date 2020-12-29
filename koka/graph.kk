module graph

import std/os/file
import std/os/path
import std/text/parse

public alias node-id = int
public alias dimacs-id = int

public alias edge = (node-id, node-id)
public val invalid-edge = (invalid-node-id, invalid-node-id)
public fun invert(e : edge) {
    (e.snd, e.fst)
}
public fun show(e : edge) : string {
    "(" + e.fst.show + ", " + e.snd.show + ")"
}

public fun raise(msg) {
    throw-exn(Exception(msg, ExnError))
}

private val max-int = 9223372036854775807;
public val invalid-node-id = max-int;
public val invalid-dimacs-id = max-int;

public fun from-dimacs-id(id : dimacs-id) : node-id {
    assert("Dimacs ID must be positive", id > 0)
    id - 1
}

public fun to-dimacs-id(id : node-id) : dimacs-id {
    assert("Node ID can't be too large", id < max-int)
    id + 1
}

private struct node {
    neighbors_ : list<node-id>
}

public fun new-node() : node {
    Node([])
}

private fun add-neighbor(n : node, id : node-id) : node {
    n( neighbors_ = Cons(id, n.neighbors_) )
}

public fun degree(n : node) : int {
    n.neighbors_.length
}

public fun neighbors(n : node) : list<node-id> {
    n.neighbors_
}

public alias graph = graph_
private struct graph_ {
    nodes_ : vector<node>
    num_edges_ : int
}

public fun new-graph(num_nodes : int) : graph {
    Graph_(vector(num_nodes, new-node()), 0)
}

public fun num-nodes(g : graph) : int {
    g.nodes_.length
}

public fun get-node(g : graph, id : node-id) : <exn> node {
    g.nodes_[id]
}

private fun set-node(g : graph, id : node-id, value : node) : <exn> graph {
    var ns := g.nodes_
    ns[id] := value
    g(nodes_ = ns)
}

public fun add-edge(g' : graph, id1 : node-id, id2 : node-id) : <exn> graph {
    if(id1 == id2) {
        raise("Graph class does not support loops!")
    }
    var g := g'
    val n1 = g.get-node(id1)
    g := g.set-node(id1, n1.add-neighbor(id2))
    val n2 = g.get-node(id2)
    g := g.set-node(id2, n2.add-neighbor(id1))
    g(num_edges_ = g.num_edges_ + 1)
}

public fun build-graph(dimacs : string) : <exn, div> graph {
    val lines = dimacs.lines.filter( fn(s) { s.first.string != "c" })
    val [num_nodes, _num_edges] = match(lines) {
        Nil -> raise("Could not find problem line in DIMACS string")
        Cons(x, _) -> match((parse(x.slice) {
            pstring("p edge")
            many { whitespace0(); pint() }
            }).either) {
                Right([n, e]) -> [n, e]
                _ -> raise("Unexpected format of input file")
            }
        }
    var g := new-graph(num_nodes)
    lines.tail.map fn(line) {
        match((parse(line.slice) {
            pstring("e")
            many { whitespace0(); pint() }
        }).either) {
            Right([i, j]) -> g := g.add-edge(i.from-dimacs-id, j.from-dimacs-id)
            _ -> ()
        }
    }
    return(g)
}

public fun show(g : graph) : <exn> string {
    var str := "c This encodes a graph in DIMACS format\n"
      + "p edge " + g.num-nodes().show + " " + g.num_edges_.show + "\n"
    for(0, g.num-nodes() - 1) fn(i) {
        val n = g.get-node(i)
        n.neighbors().foreach fn(j) {
            if(i < j) {
                str := str + "e " + i.to-dimacs-id.show + " " + j.to-dimacs-id.show + "\n"
            }
        }
    }
    str
}

public fun test() : <exn, div, st<h>> string {
    var g := new-graph(2)
    g.add-edge(0, 1)
    g.show()
}