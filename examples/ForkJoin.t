// Ticket lock

function makeCounter() {
    var v;
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x) {
    var v, b;
    do {
        v := [x];
        b := CAS(x, v, v + 1);
    } while (b = 0);
    return v;
}

function read(x) {
    var v;
    v := [x];
    return v;
}

function parallelIncr(x) {
    var t1, t2;
    t1 := fork incr(x);
    t2 := fork incr(x);
    join t1;
    join t2;
}
