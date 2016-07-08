// Adaption of the Michael-Scott's Queue
// -c 0 -o 4

predicate queueInvariant(v);

region Qu(s,p) {
  guards 0;
  interpretation {
    0 : p |-> x &*& QL(rs,x,_,-(n+1)) &*& (n = 0 \/ n > 0 &*& m >= 0 &*& QL(rn,n,_,m) &*& rn@OWN);
  }
  actions {}
}

region QL(r,x,v) {
  guards OWN * LIVE;
  interpretation {
    n > 0 | -(n + 1) : x |-> v &*& (x+1) |-> n &*& r@(OWN) &*& QL(rn,n,_,_);
           -1 : x |-> v &*& (x+1) |-> 0 &*& r@OWN;
            0 : x |-> v &*& (x+1) |-> 0 &*& queueInvariant(v);
    n > 0 | n : x |-> v &*& (x+1) |-> n &*& queueInvariant(v)
                &*& QL(rn,n,_,_) &*& rn@(OWN);
  }
  actions {
    n > 0 | : 0 ~> n;
    n >= 0 | OWN : n ~> -(n+1);
    n > 0 | OWN : 0 ~> -(n+1);
  }
}

function dequeueCAS(q,sentinel,head)
  requires Qu(s,q,0) &*& QL(rs,sentinel,_,-(head+1)) &*& head > 0;
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

