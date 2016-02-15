// NAME: Guarantee with permissions 5
// RESULT: ACCEPT

region Foo(r,x,perm) {
  guards %FOO;
  interpretation {
    n : x |-> n;
  }
  actions {
    l < u, perm $ permo = 1p | FOO[permo] : l ~> u;
  }
}

function foo(x)
  requires Foo(r,x,perm,_) &*& r@FOO[1p];
  ensures true;
{
  CAS(x,1,2);
}

