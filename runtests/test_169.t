// NAME: region creation backtracking exploit
// RESULT: REJECT

/* DESCRIPTION: Exposes a bug resulting from incorrect backtracking when
                a region is missing but cannot be created.
*/		

region Re(r, x, z) {
  guards 0;
  interpretation {
    0 : x = 0 ? true : (x |-> z  &*& Re(next,z,_,0));
  }
  actions {
  }
}

function foo(x, y)
  requires Re(r,x,42,0) &*& x > 0;
  ensures Re(r,x,42,0);
{
  [x] := y;  
}
