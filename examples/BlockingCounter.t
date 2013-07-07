// Blocking counter

function makeCounter() {
    local v;
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x) {
    local v, b;
    do {
        v := [x];
    } while (v = -1 or CAS(x, v, -1) = 0);
    [x] := v + 1;
    return v;
}

function read(x) {
    local v;
    do {
        v := [x];
    } while (v = -1);
    return v;
}
