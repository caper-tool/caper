// Binary tree

predicate treeInvariant(v);

region Tree(r,x) {
  guards 0;
  interpretation {
    0 : x |-> root &*& TreeNode(n,root,_,0) &*& n@OWN;
  }
  actions {}
}

region TreeNode(s,y,val) {
  guards OWN;
  interpretation {
    0 : y = 0 ? true : y |-> val &*& (y + 1) |-> z &*& (y + 2) |-> w &*& TreeNode(n,z,_,0) &*& n@OWN &*& TreeNode(m,w,_,0) &*& m@OWN &*& treeInvariant(val);
  }
  actions {}
}

function innerInsert(x,y)
  requires Tree(r,x,0) &*& y |-> v &*& y+1 |-> 0 &*& y+2 |-> 0 &*& treeInvariant(v);
  ensures Tree(r,x,0);
{
  t := [x];
  if (t = 0) {
    cr := CAS(x,t,y);
    if (cr != 0) {
      return;
    }
  }
  innerInsert(x,y);/*
  t := [x];
  if (t = 0) {
    cr := CAS(x,t,y);
  }
  if (cr = 0) {
    innerPush(x, y);
  }*/
}

function insert(x, v)
  requires Tree(r,x,0) &*& treeInvariant(v);
  ensures Tree(r,x,0);
{
  y := alloc(3);
  [y] := v;
  [y + 1] := 0;
  [y + 2] := 0;
  innerInsert(x, y);
}

/*
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
*/
