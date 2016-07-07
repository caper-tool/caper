// Stack-based bag

predicate bagInvariant(v);

region Tree(r,x) {
  guards 0;
  interpretation {
    0 : x |-> head &*& TreeNode(bl,head,_,0) &*& bl@OWN;
  }
  actions {}
}

region TreeNode(s,y,z) {
  guards OWN;
  interpretation {
    0 : y = 0 ? true : y |-> val &*& (y + 1) |-> z &*& Node(t,z,_,0) &*& t@OWN &*& bagInvariant(val);
    1 : s@OWN &*& y |-> val &*& (y + 1) |-> z &*& BagList(xtbl,z,_,_);
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
  if (cr = 0) {
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
  if (cr = 0) {
    ret := pop(x);
    return ret;
  }
  ret := [t];
  return ret;
}

