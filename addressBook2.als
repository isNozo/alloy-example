module tour/addressBook2
open util/ordering [Book]

abstract sig Target {}
sig Addr extends Target {}
abstract sig Name extends Target {}

sig Alias, Group extends Name {}
sig Book {
    names: set Name,
    addr: names -> some Target
}{
    no n: Name | n in n.^(addr)
    all a: Alias | lone a.addr
}

pred add (b1, b2: Book, n: Name, t: Target) {
    t in Addr or some lookup [b1, t]
    b2.addr = b1.addr + n -> t
}
pred del (b1, b2: Book, n: Name, t: Target) {
    no b1.addr.n or some n.(b1.addr) - t
    b2.addr = b1.addr - n -> t
}
fun lookup (b: Book, n: Name): set Addr {
    n.^(b.addr) & Addr
}

pred init (b: Book) {no b.addr}

fact traces {
    init [first]
    all b1: Book - last | 
    let b2 = next [b1] |
    some n: Name, t: Target |
    add [b1, b2, n, t] or
    del [b1, b2, n, t]
}

assert lookupYields {
    all b: Book, n: b.names | some lookup [b, n]
}
check lookupYields for 6

assert delUndoesAdd {
    all b1, b2, b3: Book, n: Name, t: Target |
        no n.(b1.addr) and 
        add [b1, b2, n, t] and 
        del [b2, b3, n, t] implies
        b1.addr = b3.addr
}
check delUndoesAdd for 4

assert addLocal {
    all b1, b2: Book, n1, n2: Name, t: Target |
        add [b1, b2, n1, t] and
        n1 != n2 implies
        lookup [b1, n2] = lookup [b2, n2]
}
check addLocal for 4

pred show {}
run show for 4