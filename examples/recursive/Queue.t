// Adaption of the Michael-Scott's Queue

predicate queueInvariant(v);

region Queue(r, x) {
  guards 0;
  interpretation {
    0 : x |-> head &*& QueueList(bl, head, _, _, 0) &*& bl@OWN;
  }
  actions {}
}

region QueueList(s, y, nxt, z) {
  guards OWN;
  interpretation {
    0 : y = 0 ? true : y |-> val &*& (y + 1) |-> z &*& QueueList(nxt, z, _, _, 0) &*& nxt@OWN &*& queueInvariant(val);
    1 : s@OWN &*& y |-> val &*& (y + 1) |-> z &*& QueueList(nxt, z, _, _, _);
  }
  actions {
    OWN : 0 ~> 1;
  }
}

function makeQueue()
  requires true;
  ensures Queue(r, x, 0);
{
  x := alloc(1);
  [x] := 0;
  return x;
}

function enqueue(x, v)
  requires Queue(r, x, 0) &*& queueInvariant(v);
  ensures Queue(r, x, 0);
{
  y := alloc(2);
  [y] := v;
  [y + 1] := 0;
  innerEnqueue(x, y);
}

function innerEnqueue(x, y)
  requires Queue(r, x, 0) &*& y |-> v &*& (y + 1) |-> 0 &*& queueInvariant(v);
  ensures Queue(r, x, 0);
{
  h := [x];
  if (h = 0) {
  	cr := CAS(x, 0, y);
  	if (cr = 0) {
  		innerEnqueue(x, y);
  	}
  	return;
  }
  t := getTail(h);
  cr := CAS(t + 1, 0, y);
  if (r = 0) {
    innerEnqueue(x, y);
  }
}

function getTail(x)
  requires QueueList(s, x, _, _, _) &*& x > 0;
  ensures QueueList(t, ret, _, _, _) &*& ret > 0;
{
  n := [x + 1];
  if (n = 0) {
    return x;
  } else {
    t := getTail(n);
    return t;
  }
}

function dequeue(x)
  requires Queue(r, x, 0);
  ensures ret = 0 ? Queue(r, x, 0) : Queue(r, x, 0) &*& queueInvariant(ret);
{
  h := [x];
  if (h = 0) {
    return 0;
  }
  n := [h + 1];
  cr := CAS(x, h, n);
  if (cr = 0) {
    ret := dequeue(x);
    return ret;
  }
  ret := [h];
  return ret;
}
