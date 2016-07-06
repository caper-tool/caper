// Stack

region Stack(r,x) {
  guards 0;
  interpretation {
    0 : x |-> head &*& StackList(bl,head,_,_,0) &*& bl@OWN;
  }
  actions {}
}

region StackList(s,y,nxtbl,z) {
  guards OWN;
  interpretation {
    0 : y = 0 ? true : y |-> val &*& (y + 1) |-> z &*& StackList(nxtbl,z,_,_,0) &*& nxtbl@OWN;
    1 : s@OWN &*& y |-> val &*& (y + 1) |-> z &*& StackList(nxtbl,z,_,_,_);
  }
  actions {
    OWN : 0 ~> 1;
  }
}

function push(x,v)
  requires Stack(r,x,0);
  ensures Stack(r,x,0);
{
  y := alloc(2);
  [y] := v;
  innerPush(x,y);
}

function innerPush(x,y)
  requires Stack(r,x,0) &*& y |-> v &*& y+1 |-> _;
  ensures Stack(r,x,0);
{
  t := [x];
  [y + 1] := t;
  cr := CAS(x,t,y);
  if (cr = 0) {
    innerPush(x, y);
  }
}

function pop(x)
  requires Stack(r,x,0);
  ensures Stack(r,x,0);
{
  t := [x];
  if (t = 0) {
    return 0;
  }
  t2 := [t + 1];
  cr := CAS(x,t,t2);
  if (cr = 0) {
    ret := pop(x);
    return ret;
  }
  ret := [t];
  return ret;
}

