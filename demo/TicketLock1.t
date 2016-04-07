// Ticket Lock

region TLock(r,x) {
    guards #TICKET;
    interpretation {
        n : x |-> m &*& (x+1) |-> n &*& m >= n &*& r@TICKET{i | i >= m};
    }
    actions {
        t0 < t1 | TICKET{i | i >= t0, i < t1} : t0 ~> t1;
    }
}

// Create a ticket lock
function makeLock()
    requires true;
    ensures TLock(r,ret,_);
{
    v := alloc(2);
    [v + 0] := 0; // Available ticket
    [v + 1] := 0; // Ticket that currently holds the lock ("now serving")
    return v;
}
// Take a ticket
function incr(x)
    requires TLock(r,x,_);
    ensures TLock(r,x,i) &*& r@TICKET(ret) &*& ret >= i;
{
    t := [x + 0];
    // Try to increment the ticket counter
    b := CAS(x + 0, t, t + 1);
    if (b = 0) {
        t := incr(x); // Retry if we fail
    }
    return t;
}
// Wait for ticket to acquire lock
function wait(x, t)
    requires TLock(r,x,i) &*& r@TICKET(t) &*& t >= i;
    ensures TLock(r,x,t) &*& r@TICKET(t);
{
    v := [x + 1];
    if (v < t) {
        wait(x, t);
    }
}

// Acquire the lock
function lock(x)
    requires TLock(r,x,_);
    ensures TLock(r,x,t) &*& r@TICKET(t);
{
    t := incr(x);
    wait(x, t);
}

// Release the lock
function unlock(x)
    requires TLock(r,x,t) &*& r@TICKET(t);
    ensures TLock(r,x,_);
{
    // Increment "now serving"
    v := [x + 1];
    [x + 1] := v + 1;
}

