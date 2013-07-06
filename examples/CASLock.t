// Compare-and-swap lock

makeLock() {
    local v;
    v := alloc(1);
    [v] := 0;
    return v;
}

lock(x) {
    local b;
    do {
        b := CAS(x, 0, 1);
    } while (b = false);
}

unlock(x) {
    [x] := 0;
}
