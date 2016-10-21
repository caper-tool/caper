// Adaptation of the Michael-Scott Queue
// -o 3 -c 2
// Almost certainly requires increase of Z3 timeout (more than 1s)

predicate queueInvariant(v);

region Qu(s,p) {
  guards 0;
  interpretation {
    0 : p |-> x &*& QL(rs,x,_,3*n+1) &*& n >= 0 &*& rs@OWN;
  }
  actions {}
}

region QL(r,x,v) {
  guards OWN;
  interpretation {
                0 : x |-> v &*& (x+1) |-> 0 &*& queueInvariant(v);
                1 : x |-> v &*& (x+1) |-> 0;
    n > 0 | 3 * n : x |-> v &*& (x+1) |-> n &*& queueInvariant(v) &*& QL(rn,n,_,3*b) &*& rn@OWN;
    n > 0 | 3*n+1 : x |-> v &*& (x+1) |-> n &*& QL(rn,n,_,3*b) &*& rn@OWN;
    n > 0 | 3*n+2 : x |-> v &*& (x+1) |-> n &*& r@OWN &*& QL(rn,n,_,_);
  }
  actions {
    n > 0  |     : 0 ~> 3*n;
    n > 0  |     : 1 ~> 3*n+1;
    n >= 0 | OWN : 3*n ~> 3*n+1;
    n > 0  | OWN : 3*n+1 ~> 3*n+2;
    n > 0  | OWN : 3*n ~> 3*n+2;
    n >= 3 | OWN : 0 ~> n;
    n > 0  | OWN : 1 ~> 3*n+2;
  }
}

function makeQueue()
  requires true;
  ensures Qu(r, ret, 0);
{
  y := alloc(2);
  [y + 1] := 0;
  x := alloc(1);
  [x] := y;
  return x;
}

function enqueue(x, v)
  requires Qu(r, x, 0) &*& queueInvariant(v);
  ensures Qu(r, x, 0);
{
  y := alloc(2);
  [y] := v;
  [y + 1] := 0;
  innerEnqueue(x, y);
}

function innerEnqueue(x, y)
  requires Qu(r, x, 0) &*& y |-> v &*& (y + 1) |-> 0 &*& queueInvariant(v);
  ensures Qu(r, x, 0);
{
  h := [x];
  t := getTail(h);
  cr := CAS(t + 1, 0, y);
  if (cr = 0) {
    innerEnqueue(x, y);
  }
}

function getTail(x)
  requires QL(s, x, _, _) &*& x > 0;
  ensures QL(t, ret, _, _) &*& ret > 0;
{
  n := [x + 1];
  if (n = 0) {
    return x;
  } else {
    t := getTail(n);
    return t;
  }
}

function dequeue(q)
  requires Qu(s,q,0);
  ensures ret = 0 \/ queueInvariant(ret);
{
  sentinel := [q];
  head := [sentinel + 1];
  if (head = 0) {
    return 0;
  } else {
    r := CAS(q,sentinel,head);
    if (r = 0) {
      res := dequeue(q);
      return res;
    } else {
      res := [head];
      return res;
    }
  }
}
