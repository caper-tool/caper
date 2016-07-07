// NAME: region creation states 2
// RESULT: ACCEPT

/* DESCRIPTION: Exposes a bug resulting from the order of how the interpretation of the states is defined.
*/		

predicate queueInvariant(v);

region Queue(r, x) {
  guards 0;
  interpretation {
    0 : x |-> head &*& QueueList(s, head, -1) &*& s@OWN;
  }
  actions {}
}

region QueueList(s, y) {
  guards OWN;
  interpretation {
    -1 : y |-> _ &*& (y + 1) |-> n &*& (z = 0 ? true : QueueList(nxt, n, _));
    n >= 0 | n : y |-> val &*& (y + 1) |-> n &*& (n = 0 ? true : QueueList(nxt, n, m) &*& nxt@OWN &*& queueInvariant(val));
  }
  actions {
    OWN: 0 ~> n;
    n >= 0 | OWN : n ~> -1;
  }
}

function makeList()
  requires true;
  ensures QueueList(r, ret, -1) &*& r@OWN;
{
  y := alloc(2);
  [y + 1] := 0;
  return y;
}
