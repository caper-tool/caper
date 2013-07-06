// Blocking counter

makeCounter() {
    local v;
    v := alloc(1);
    [v] := 0;
    return v;
}

incr(x) {
    local v, b;
    do {
        v := [x];
        b := v != 1 and CAS(x, v, -1);
    } while (b = false);
    [x] := v + 1;
    return v;
}

read(x) {
    local v;
    do {
        v := [x];
    } while (v = -1);
    return v;
}
