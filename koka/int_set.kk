module int_set

// The red-black tree from the koka/samples folder adopted to work as a set.

private type color {
  Red
  Black
}

public type int-set {
  Leaf
  Node(color : color, left : int-set, key : int, right : int-set)
}

private fun is-red(t : int-set) : bool {
  match(t) {
    Node(Red) -> True
    _         -> False
  }
}

private fun balance-left(l:int-set, k: int, r: int-set): int-set {
  match(l) {
    Leaf -> Leaf
    Node(_, Node(Red, lx, kx, rx), ky, ry)
      -> Node(Red, Node(Black, lx, kx, rx), ky, Node(Black, ry, k, r))
    Node(_, ly, ky, Node(Red, lx, kx, rx))
      -> Node(Red, Node(Black, ly, ky, lx), kx, Node(Black, rx, k, r))
    Node(_, lx, kx, rx)
      -> Node(Black, Node(Red, lx, kx, rx), k, r)
  }
}

private fun balance-right(l: int-set, k: int, r: int-set): int-set {
  match(r) {
    Leaf -> Leaf
    Node(_, Node(Red, lx, kx, rx), ky, ry)
      -> Node(Red, Node(Black, l, k, lx), kx, Node(Black, rx, ky, ry))
    Node(_, lx, kx, Node(Red, ly, ky, ry))
      -> Node(Red, Node(Black, l, k, lx), kx, Node(Black, ly, ky, ry))
    Node(_, lx, kx, rx)
      -> Node(Black, l, k, Node(Red, lx, kx, rx))
  }
}

private fun ins(t: int-set, k: int): int-set {
  match(t) {
    Leaf -> Node(Red, Leaf, k, Leaf)
    Node(Red, l, kx, r)
      -> if (k < kx) then Node(Red, ins(l, k), kx, r)
         elif (k == kx) then Node(Red, l, k, r)
         else Node(Red, l, kx, ins(r, k))
    Node(Black, l, kx, r)
      -> if (k < kx) then (if (is-red(l)) then balance-left(ins(l,k), kx, r)
                                          else Node(Black, ins(l, k), kx, r))
         elif (k == kx) then Node(Black, l, k, r)
         elif (is-red(r)) then balance-right(l, kx, ins(r,k))
         else Node(Black, l, kx, ins(r, k))
  }
}

private fun set-black(t: int-set) : int-set {
  match(t) {
    Node(_, l, k, r) -> Node(Black, l, k, r)
    _ -> t
  }
}

// Tree insertion
public fun insert(t : int-set, k : int) : int-set {
  if (is-red(t))
    then set-black(ins(t, k))
    else ins(t, k)
}

public fun contains(t : int-set, k : int) : bool {
    match(t) {
        Leaf -> False
        Node(_, l, kx, r)
          -> if(k < kx) then l.contains(k)
             elif (k == kx) then True
             else r.contains(k)
    }
}

public val empty-int-set = Leaf