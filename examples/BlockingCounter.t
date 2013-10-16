// Blocking counter

function makeCounter() {
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x) {
    do {
        v := [x];
        if (v = -1) {
            b := 0;
        } else {
            b := CAS(x, v, -1);
        }
    } while (b = 0);
    [x] := v + 1;
    return v;
}

function read(x) {
    do {
        v := [x];
    } while (v = -1);
    return v;
}
