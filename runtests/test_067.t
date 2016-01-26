// NAME: Value variable as region state test 1
// RESULT: ACCEPT

/* DESCRIPTION: This tests if Caper can deal with conditionals in the precondition that have regions with a value partially defined before.
 */
 
region Node(r, x) {
  guards SET;
  interpretation {
    0 : x |-> v &*& x + 1 |-> 0;
    n > 0 | n : x |-> v &*& x + 1 |-> n &*& Node(s, n, _);
  }
  actions {
    n >= 0, m >= 0 | SET : n ~> m;
  }
}

function set_next(x, n)
  requires Node(r, x, m) &*& r@(SET) &*& m >= 0 &*& n >= 0 &*& (n = 0 ? true : Node(s, n, _));
  ensures Node(r, x, n) &*& r@(SET);
{
    [x + 1] := n;
}
