// Ticket lock

function makeLock() {
    v := alloc(2);
    n := makeCounter();
    t := makeCounter();
    [v + 0] := n;
    [v + 1] := t;
    return v;
}

function lock(x) {
    n := [x + 0];
    t := [x + 1];
    v := incr(t);
    do {
        w := read(n);
    } while (v != w);
}

function unlock(x) {
    n := [x + 0];
    incr(n);
}
