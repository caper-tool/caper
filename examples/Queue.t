// Adaption of the Michael-Scott's Queue

predicate queueInvariant(v);

region Queue(r, x) {
  guards 0;
  interpretation {
    0 : x |-> head &*& QueueList(s, head, n) &*& s@OWN &*& n >= 0; 
  }
  actions {}
}

region QueueList(s, y) {
  guards OWN;
  interpretation {
    0 : y |-> _ &*& (y + 1) |-> 0;
    n > 0 | n : y |-> val &*& (y + 1) |-> n &*& QueueList(nxt, n, m) &*& nxt@OWN &*& queueInvariant(val);
    n < 0 | n : y |-> val &*& (y + 1) |-> -n &*& QueueList(nxt, -n, m);
  }
  actions {
    OWN: 0 ~> n;
    n > 0 | OWN: n ~> -n; 
  }
}
/*
function makeQueue()
  requires true;
  ensures Queue(r, ret, 0);
{
  y := alloc(2);
  [y + 1] := 0;
  x := alloc(1);
  [x] := y;
  return x;
}*/
/*
function enqueue(x, v)
  requires Queue(r, x, 0) &*& queueInvariant(v);
  ensures Queue(r, x, 0);
{
  y := alloc(2);
  [y] := v;
  [y + 1] := 0;
  innerEnqueue(x, y);
}
*//*
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
*//*
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
*/
function dequeue(x)
  requires Queue(r, x, 0);
  ensures ret = 0 ? Queue(r, x, 0) : Queue(r, x, 0) &*& queueInvariant(ret);
{
  h := [x];
  assert Queue(r, x, 0) &*& QueueList(s, h, m);
  n := [h + 1];
  assert Queue(r, x, 0) &*& QueueList(s, h, m) &*& (n = 0 ? true : m = n \/ m = -n);
  if (n = 0) {
    return 0;
  } else {
//    assert Queue(r, x, 0) &*& QueueList(s, h, m) &*& ;
//    assert Queue(r, x, 0) &*& QueueList(s, h, m) &*& QueueList(t, n, _) &*& m != 0;
//    cr := dequeueCAS(x, h, n);
//    if (cr = 0) {
//      ret := dequeue(x);
//      return ret;
//    } else {
//    ret := [n];
//      ret := dequeue(x);
//      return cr;
      cr := dequeue(x);
      return cr;
//    }
  }
}
/*
function dequeueCAS(x, h, n)
  requires Queue(r, x, 0) &*& QueueList(s, h, n) &*& QueueList(t, n,_) &*& n != 0;
  ensures ret = 0 \/ queueInvariant(v);
{
  cr := dequeueCAS(x, h, n);
  return cr;
}*/
/*
function dequeueCAS(x, h, n)
  requires Queue(r, x, 0) &*& QueueList(s, h, m) &*& m < 0 &*& QueueList(t, n, _) &*& m != 0 &*& (m = -n \/ m = n);
  ensures ret = 0 \/ bagInvariant(v);
{
  cr := CAS(x, h, n);
  return cr;
}
*/