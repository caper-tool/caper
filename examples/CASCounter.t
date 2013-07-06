// Compare-and-swap counter

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
        b := CAS(x, v, v + 1);
    } while (b = false);
    return v;
}

read(x) {
    local v;
    v := [x];
    return v;
}
