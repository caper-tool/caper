// Adaption of the Michael-Scott's Queue
// -c 0 -o 4

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
    n >= 0, 0 <= k, k < 3 | 3*n + k : x |->v &*& (x+1) |-> n &*& x != n &*&
                            ((k = 2) ? (n > 0 &*& r@OWN &*& QL(rn,n,_,_)) :
                              ((n > 0 ? QL(rn,n,_,3*b) &*& rn@OWN : true) &*& (k = 0 ? queueInvariant(v) : true)));
/*                0 : x |-> v &*& (x+1) |-> 0 &*& queueInvariant(v);
                1 : x |-> v &*& (x+1) |-> 0;
    n > 0 | 3 * n : x |-> v &*& (x+1) |-> n &*& queueInvariant(v) &*& QL(rn,n,_,3*b) &*& rn@OWN;
    n > 0 | 3*n+1 : x |-> v &*& (x+1) |-> n &*& QL(rn,n,_,3*b) &*& rn@OWN;
    n > 0 | 3*n+2 : x |-> v &*& (x+1) |-> n &*& r@OWN &*& QL(rn,n,_,_); */
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

function dequeueCAS(q,sentinel,head)
  requires Qu(a,q,0) &*& QL(rs,sentinel,_,3*head+z) &*& head > 0 &*& 1 <= z &*& z < 3;
  ensures ret = 0 \/ (QL(rh,head,v,_) &*& queueInvariant(v));

{
  r := CAS(q,sentinel,head);
  return r;
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
    r := dequeueCAS(q,sentinel,head);
    if (r = 0) {
      res := dequeue(q);
      return res;
    } else {
      res := [head];
      return res;
    }
  }
}

