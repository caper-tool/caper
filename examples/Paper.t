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

function makeMCL() {
    l := makeLock();
    return l;
}

function read(l, x) {
    lock(l);
    v := [x];
    unlock(l);
    return v;
}

function write(l, x, v) {
    lock(l);
    [x] := v;
    unlock(l);
    return v;
}


function cas(l, x, v1, v2) {
    lock(l);
    v := [x];
    if (v = v1) {
        [x] := v2;
        r := 1;
    } else {
        r := 0;
    }
    unlock(l);
    return r;
}

function dcas(l, x, y, v1, w1, v2, w2) {
    lock(l);
    v := [x];
    w := [y];
    if (v = v1 and w = w1) {
        [x] := v2;
        [y] := w2;
        r := 1;
    } else {
        r := 0;
    }
    unlock(l);
    return r;
}

// The "Snark" Linked-list Deque

function makeNode(left, right, value) {
    node := alloc(3);
    [node + 0] := left;
    [node + 1] := right;
    [node + 2] := value;
    return node;
}

function makeDeque() {
    lock := makeMCL();
    dummy := makeNode(0, 0, 0);
    [dummy + 0] := dummy;
    [dummy + 1] := dummy;
    deque := alloc(4);
    [deque + 0] := dummy; // leftHat
    [deque + 1] := dummy; // rightHat
    [deque + 2] := dummy;
    [deque + 3] := lock;
    return deque;
}

function pushRight(deque, value) {
    lock := [deque + 3];
    dummy := [deque + 2];
    node := makeNode(0, dummy, value);
//    v := 1;
//    while (v < 1000 * (20 - value)) {
//    	v := v + 1;
//	}
	while (true) {
        rightHat := read(lock, deque + 1);
        rightHatR := read(lock, rightHat + 1);
        if (rightHatR = rightHat) {
            [node + 0] := dummy;
            leftHat := read(lock, deque + 0);
            b := dcas(lock, deque + 1, deque + 0, rightHat, leftHat, node, node);
            if (b = 1) {
                return 1;
            }
        } else {
            [node + 0] := rightHat;
            b := dcas(lock, deque + 1, rightHat + 1, rightHat, rightHatR, node, node);
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
        rightHat := read(lock, deque + 1);
        leftHat := read(lock, deque + 0);
        rightHatR := read(lock, rightHat + 1);
        if (rightHatR = rightHat) {
            return 0; // empty
        }
        if (rightHat = leftHat) {
            b := dcas(lock, deque + 1, deque + 0, rightHat, leftHat, dummy, dummy);
            if (b = 1) {
                value := read(lock, rightHat + 2);
                return value;
            }
        } else {
            rightHatL := read(lock, rightHat + 0);
            b := dcas(lock, deque + 1, rightHat + 0, rightHat, rightHatL, rightHatL, rightHat);
            if (b = 1) {
                value := read(lock, rightHat + 2);
                write(lock, rightHat + 1, dummy);
                return value;
            }
        }
    }
}

function pushLeft(deque, value) {
    lock := [deque + 3];
    dummy := [deque + 2];
    node := makeNode(dummy, 0, value);
    while (true) {
        leftHat := read(lock, deque + 0);
        leftHatL := read(lock, leftHat + 0);
        if (leftHatL = leftHat) {
            [node + 1] := dummy;
            rightHat := read(lock, deque + 1);
            b := dcas(lock, deque + 0, deque + 1, leftHat, rightHat, node, node);
            if (b = 1) {
                return 1;
            }
        } else {
            [node + 1] := leftHat;
            b := dcas(lock, deque + 0, leftHat + 0, leftHat, leftHatL, node, node);
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
        leftHat := read(lock, deque + 0);
        rightHat := read(lock, deque + 1);
            v := 1;
    while (v < 100000) {
    	v := v + 1;
	}

        leftHatL := read(lock, leftHat + 0);
        if (leftHatL = leftHat) {
        print(9999);
            return 0; // empty
        }
        if (leftHat = rightHat) {
            b := dcas(lock, deque + 0, deque + 1, leftHat, rightHat, dummy, dummy);
            if (b = 1) {
                value := read(lock, leftHat + 2);
                return value;
            }
        } else {
            leftHatR := read(lock, leftHat + 1);
            b := dcas(lock, deque + 0, leftHat + 1, leftHat, leftHatR, leftHatR, leftHat);
            if (b = 1) {
                value := read(lock, leftHat + 2);
                write(lock, leftHat + 0, dummy);
                return value;
            }
        }
    }
}

function recursivePrint(node) {
    leftNode := [node + 0];
    if (leftNode = node) {
        return 0;
    }
    value := [node + 2];
    print(value);
    nextNode := [node + 1];
    recursivePrint(nextNode);
}

// not to run in parallel! here just to make sure it works...
function printDeque(deque) {
    leftNode := [deque + 0];    
    print(10000000001);
    recursivePrint(leftNode);
    print(10000000001);
}

function main() {
    deque := makeDeque();
    pushLeft(deque, 30);
    pushLeft(deque, 40);
    fork popLeft(deque);
    pushLeft(deque, 50);
    pushLeft(deque, 60);
    v := 1;
	while (v < 3) {
	    fork popRight(deque);
	    v := v + 1;
	}
    v := 1;
    while (v < 100000) {
    	v := v + 1;
    }
    printDeque(deque);
}
