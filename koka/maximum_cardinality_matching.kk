module maximum_cardinality_matching

import graph
import matching
import components
import unshrinking
import perfect_matching

import std/os/path
import std/os/file
import std/os/env

public fun max-cardinality-matching(g : graph) : <st<h>, exn, div> matching {
    var to-ignore := vector(g.num-nodes, False)
    var m := new-matching(g.num-nodes)
    until-just {
        match(perfect-matching(g, m, to-ignore)) {
            Nothing -> Just(m)
            Just(frtree) -> {
                to-ignore[frtree.root] := True
                for(0, g.num-nodes - 1) fn(i) {
                    if(frtree.is-even[i] || frtree.is-odd[i]) {
                        to-ignore[i] := True
                    }
                }
                Nothing
            }
        }
    }
}

// public fun main(argc : int, argv : list<string>) {
public fun main() {
    val argv = get-argv()
    with except throw-exn(e) {
        println(e.message)
        return 1
    }
    match(argv[1]) {
        Nothing -> {
            println("Program call: <program_name> <input_graph>")
            return 1
        }
        Just(f) -> {
            val path = path(".") + f
            val dimacs = read-text-file(path)
            val g = build-graph(dimacs)
            val m = g.max-cardinality-matching()
            println(m.cardinality().show)
            return 0
        }
    }
}