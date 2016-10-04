// NAME: Permission nonsense 3
// RESULT: REJECT

// DESCRIPTION: Tests permission compatability stuff

region Foo(r,x,p1,p2) {
  guards %PERM;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1;
  }
  actions {
    PERM[p2] : 0 ~> 1;
    PERM[p1] : 1 ~> 0;
  }
}

function foo(x)
  requires Foo(r,x,p1,p2,0) &*& r@PERM[p3] &*& p3 = p1 $ p4;
  ensures Foo(r,x,p1,p2,1);
{
  [x] := 1;
}
