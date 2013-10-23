// Lock

function makeLock() {
    v := alloc(1);
    [v] := 0;
    return v;
}

function lock(x) {
    do {
        b := CAS(x, 0, 1);
    } while (b = 0);
}

function unlock(x) {
    [x] := 0;
}

// DCAS

function read(l, x) {
    tmp := lock(l);
    v := [x];
    tmp := unlock(l);
    return v;
}

function write(l, x, v) {
    tmp := lock(l);
    [x] := v;
    tmp := unlock(l);
    return v;
}


function cas(l, x, v1, v2) {
    tmp := lock(l);
    v := [x];
    if (v = v1) {
        [x] := v2;
        r := 1;
    } else {
        r := 0;
    }
    tmp := unlock(l);
    return r;
}

function dcas(l, x, y, v1, w1, v2, w2) {
    tmp := lock(l);
    v := [x];
    w := [y];
    if (v = v1 and w = w1) {
        [x] := v2;
        [y] := w2;
        r := 1;
    } else {
        r := 0;
    }
    tmp := unlock(l);
    return r;
}

// The "Snark" Linked-list Deque

function makeNode() {
    node := alloc(3);
    return node;
}

function makeDeque() {
    lock := makeLock();
    dummy := makeNode();
    [dummy + 0] := dummy;
    [dummy + 1] := dummy;
    deque := alloc(4);
    [deque + 0] := dummy; // rightHat
    [deque + 1] := dummy; // leftHat
    [deque + 2] := dummy;
    [deque + 3] := lock;
    return deque;
}

function pushRight(deque, value) {
    lock := [deque + 3];
    dummy := [deque + 2];
    node := makeNode();
    [node + 0] := dummy;
    [node + 2] := value;
    while (true) {
        rightHat := read(lock, deque + 0);
        rightHatR := read(lock, rightHat + 0);
        if (rightHatR = rightHat) {
            [node + 1] := dummy;
            leftHat := read(lock, deque + 1);
            b := dcas(lock, deque + 0, deque + 1, rightHat, leftHat, node, node);
            if (b = 1) {
                return 1;
            }
        } else {
            [node + 1] := rightHat;
            b := dcas(lock, deque + 0, rightHat + 0, rightHat, rightHatR, node, node);
            if (b = 1) {
                return 1;
            }
        }
    }
}

function popRight(deque) {
    lock := [deque + 3];
    dummy := [deque + 2];
    while (true) {
        rightHat := read(lock, deque + 0);
        leftHat := read(lock, deque + 1);
        rightHatR := read(lock, rightHat + 0);
        if (rightHatR = rightHat) {
            return 0; // empty
        }
        if (rightHat = leftHat) {
            b := dcas(lock, deque + 0, deque + 1, rightHat, leftHat, dummy, dummy);
            if (b = 1) {
                value := read(lock, rightHat + 2);
                return value;
            }
        } else {
            rightHatL := read(lock, rightHat + 1);
            b := dcas(lock, deque + 0, rightHat + 1, rightHat, rightHatL, rightHatL, rightHat);
            if (b = 1) {
                value := read(lock, rightHat + 2);
                tmp := write(lock, rightHat + 0, dummy);
                return value;
            }
        }
    }
}

function pushLeft(deque, value) {
    lock := [deque + 3];
    dummy := [deque + 2];
    node := makeNode();
    [node + 1] := dummy;
    [node + 2] := value;
    while (true) {
        leftHat := read(lock, deque + 1);
        leftHatL := read(lock, leftHat + 1);
        if (leftHatL = leftHat) {
            [node + 0] := dummy;
            rightHat := read(lock, deque + 0);
            b := dcas(lock, deque + 1, deque + 0, leftHat, rightHat, node, node);
            if (b = 1) {
                return 1;
            }
        } else {
            [node + 0] := leftHat;
            b := dcas(lock, deque + 1, leftHat + 1, leftHat, leftHatL, node, node);
            if (b = 1) {
                return 1;
            }
        }
    }
}

function popLeft(deque) {
    lock := [deque + 3];
    dummy := [deque + 2];
    while (true) {
        leftHat := read(lock, deque + 1);
        rightHat := read(lock, deque + 0);
        leftHatL := read(lock, leftHat + 1);
        if (leftHatL = leftHat) {
            return 0; // empty
        }
        if (leftHat = rightHat) {
            b := dcas(lock, deque + 1, deque + 0, leftHat, rightHat, dummy, dummy);
            if (b = 1) {
                value := read(lock, leftHat + 2);
                return value;
            }
        } else {
            leftHatR := read(lock, leftHat + 0);
            b := dcas(lock, deque + 1, leftHat + 0, leftHat, leftHatR, leftHatR, leftHat);
            if (b = 1) {
                value := read(lock, leftHat + 2);
                tmp := write(lock, leftHat + 1, dummy);
                return value;
            }
        }
    }
}

function recursivePrint(node) {
    leftNode := [node + 1];
    if (leftNode = node) {
        return 0;
    }
    value := [node + 2];
    tmp := print(value);
    nextNode := [node + 0];
    tmp := recursivePrint(nextNode);
}

// not to run in parallel! here just to make sure it works...
function printDeque(deque) {
    leftNode := [deque + 1];    
    tmp := print(10000000001);
    tmp := recursivePrint(leftNode);
    tmp := print(10000000001);
}

function main() {
    deque := makeDeque();
    tmp := pushRight(deque, 9);
    tmp := popLeft(deque);
    tmp := print(tmp);
}
