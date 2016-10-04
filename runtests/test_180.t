// NAME: Permission nonsense 4
// RESULT: ACCEPT

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
  requires p1 != 0p &*& !(p2 # p2) &*& Foo(r,x,p1,p2,0) &*& r@PERM[p3] &*& p3 = p1 $ p2;
  ensures Foo(r,x,p1,p2,1);
{
  [x] := 1;
}
