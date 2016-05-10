// Stack-based bag

predicate bagInvariant(v);

region Bag(r,x) {
  guards 0;
  interpretation {
    0 : x |-> y &*& BagList(s,y,_,0) &*& s@OWN;
  }
  actions {}
}

region BagList(s,y,z) {
  guards OWN;
  interpretation {
    0 : y = 0 ? true : y |-> v &*& (y + 1) |-> z &*& BagList(t,z,_,0) &*& t@OWN &*& bagInvariant(v);
    1 : s@OWN &*& y |-> v &*& (y + 1) |-> z &*& BagList(t,z,_,_);
  }
  actions {
    OWN : 0 ~> 1;
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

function innerPush(x,y)
  requires Bag(r,x,0) &*& y |-> v &*& y+1 |-> _ &*& bagInvariant(v);
  ensures Bag(r,x,0);
{
  t := [x];
  [y + 1] := t;
  cr := CAS(x,t,y);
  if (cr != 1) {
    innerPush(x, y);
  }
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
  cr := CAS(x,t,t2);
  if (cr != 1) {
    ret := pop(x);
    return ret;
  }
  ret := [t];
  return ret;
}

