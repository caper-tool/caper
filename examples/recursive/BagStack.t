// Stack-based bag
// Requires flags: -c 1 -o 3

predicate bagInvariant(v);

region Bag(r,x) {
  guards 0;
  interpretation {
    0 : x |-> head &*& BagList(bl,head,_,_,0) &*& bl@OWN;
  }
  actions {}
}

region BagList(s,y,val,z) {
  guards OWN;
  interpretation {
    0 : y = 0 ? true : y |-> val &*& (y + 1) |-> z &*& BagList(nxtbl,z,_,_,0) &*& nxtbl@OWN &*& bagInvariant(val);
    1 : s@OWN &*& y |-> val &*& (y + 1) |-> z &*& BagList(nxtbl,z,_,_,_);
  }
  actions {
    OWN : 0 ~> 1;
  }
}

function innerPush(x,y)
  requires Bag(r,x,0) &*& y |-> v &*& y+1 |-> _ &*& bagInvariant(v);
  ensures Bag(r,x,0);
{
    t := [x];
    [y + 1] := t;
    cr := CAS(x,t,y);
    if (cr = 0) {
      innerPush(x, y);
    }
}

function push(x,v)
  requires Bag(r,x,0) &*& bagInvariant(v);
  ensures Bag(r,x,0);
{
    y := alloc(2);
    [y] := v;
    innerPush(x,y);
}

function popCAS(x,t,t2)
  requires Bag(r,x,0) &*& BagList(rt,t,v,t2,_) &*& BagList(rt2,t2,_,_,_) &*& t != 0;
  ensures ret = 0 \/ bagInvariant(v);
{
    cr := CAS(x,t,t2);
    return cr;
}

function pop(x)
  requires Bag(r,x,0);
  ensures ret = 0 ? Bag(r,x,0) : Bag(r,x,0) &*& bagInvariant(ret);
{
    t := [x];
    if (t = 0) {
      return 0;
    }
    t2 := [t + 1];
    cr := popCAS(x,t,t2);
    if (cr = 0) {
      ret := pop(x);
      return ret;
    }
    ret := [t];
    return ret;
}
