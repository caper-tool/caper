// Compare-and-swap lock

function makeLock() {
    local v;
    v := alloc(1);
    [v] := 0;
    return v;
}

function lock(x) {
    local b;
    do {
        b := CAS(x, 0, 1);
    } while (b = 0);
}

function unlock(x) {
    [x] := 0;
}
