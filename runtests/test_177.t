// NAME: Permission nonsense 1
// RESULT: ACCEPT

// DESCRIPTION: Tests permission compatability stuff

region Foo(r,x,p1,p2) {
  guards %PERM;
  interpretation {
    0 : r@PERM[p1] &*& x |-> 0;
    1 : r@PERM[p2] &*& x |-> 1;
  }
  actions {
    PERM[p2] : 0 ~> 1;
    PERM[p1] : 1 ~> 0;
  }
}

function foo(x)
  requires Foo(r,x,p1,p2,0) &*& p1 # p2 &*& r@PERM[p2];
  ensures Foo(r,x,p1,p2,1) &*& r@PERM[p1];
{
  [x] := 1;
}
