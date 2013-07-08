// Ticket lock

function makeLock() {
    var v;
    v := alloc(2);
    [v + 0] := makeCounter();
    [v + 1] := makeCounter();
    return v;
}

function lock(x) {
    var v;
    v := incr([x + 1]);
    while (v != read([x + 0])) {
        skip;
    }
}

function unlock(x) {
    incr([x + 0]);
}
