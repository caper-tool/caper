// NAME: Guarantee with permissions 6
// RESULT: REJECT

/* DECRIPTION: This tests subtle permission reasoning that
               can affect the guarantee.  An update is allowed
               given the complement permission of perm (the
               permission associated with the region as a
               parameter).  Implicit in the guard requirement
               FOO[permo] is a condition that permo != 0p --
               this is by convention.  If it were the case that
               perm = 1p, then it would never be possible to
               perform such an action.

               In this example, the condition is not enforced.
*/

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

