// Compare-and-swap counter

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
        b := CAS(x, v, v + 1);
    } while (b = 0);
    return v;
}

function read(x) {
    local v;
    v := [x];
    return v;
}
