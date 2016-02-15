// NAME: Guarantee with permissions 4
// RESULT: ACCEPT

region Foo(r,x,perm) {
  guards %FOO;
  interpretation {
    n : x |-> n;
  }
  actions {
    l < u | FOO[permo] : l ~> u;
  }
}

function foo(x)
  requires Foo(r,x,perm,_) &*& r@FOO[permo];
  ensures true;
{
  CAS(x,1,2);
}

