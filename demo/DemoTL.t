// Ticket Lock

// Create a ticket lock
function makeLock()
{
    v := alloc(2);
    [v + 0] := 0; // Available ticket
    [v + 1] := 0; // Ticket that currently holds the lock ("now serving")
    return v;
}

// Take a ticket
function incr(x)
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
{
    v := [x + 1];
    if (v < t) {
        wait(x, t);
    }
}

// Acquire the lock
function lock(x)
{
    t := incr(x);
    wait(x, t);    
}


// Release the lock
function unlock(x)
{
    // Increment "now serving"
    v := [x + 1];
    [x + 1] := v + 1;
}












function setPair(x, z, w)
{
  lock(z);
  // begin critical section
  [x] := w;
  [x + 1] := w;
  // end critical section
  unlock(z);
}
