// NAME: Guarantee with permissions 1
// RESULT: REJECT

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
  requires Foo(r,x,perm,_) &*& r@FOO[p2];
  ensures true;
{
  CAS(x,1,2);
}

