// Compare-and-swap counter

function makeCounter() {
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x) {
    do {
        v := [x];
        b := CAS(x, v, v + 1);
    } while (b = 0);
    return v;
}

function read(x) {
    v := [x];
    return v;
}
