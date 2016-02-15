// NAME: Guarantee with permissions 2
// RESULT: ACCEPT

region Foo(r,x,perm) {
  guards %FOO;
  interpretation {
    n : x |-> n;
  }
  actions {
    l < u | FOO[perm] : l ~> u;
  }
}

function foo(x)
  requires Foo(r,x,perm,_) &*& r@FOO[perm];
  ensures true;
{
  CAS(x,1,2);
}

