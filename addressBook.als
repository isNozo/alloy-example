module tour/addressBook

sig Name, Addr {}
sig Book {
    addr: Name -> lone Addr
}

pred show (b: Book) {
    #b.addr > 1
    #Name.(b.addr) > 1
}
run show for 3 but 1 Book

pred add (b_pre, b_pst : Book, n: Name, a: Addr) {
    b_pst.addr = b_pre.addr + n -> a
}
run add for 3 but 2 Book

pred showAdd (b_pre, b_pst : Book, n: Name, a: Addr) {
    add [b_pre, b_pst, n ,a]
    #Name.(b_pst.addr) > 1
}
run showAdd for 3 but 2 Book

pred del (b_pre, b_pst : Book, n: Name) {
    b_pst.addr = b_pre.addr - n -> Addr
}

fun lookup (b: Book, n: Name) : set Addr {
    n.(b.addr)
}

assert delUndoesAdd {
    all b1, b2, b3: Book, n: Name, a: Addr |
        no n.(b1.addr) and 
        add [b1, b2, n, a] and 
        del [b2, b3, n] implies b1.addr = b3.addr
}
check delUndoesAdd for 4

assert addIdempotent {
    all b1, b2, b3: Book, n: Name, a: Addr |
        add [b1, b2, n, a] and
        add [b2, b3, n, a] implies
        b2.addr = b3.addr
}
check addIdempotent for 4

assert addLocal {
    all b1, b2: Book, n1, n2: Name, a: Addr |
        add [b1, b2, n1, a] and
        n1 != n2 implies
        lookup [b1, n2] = lookup [b2, n2]
}
check addLocal for 4
