// NAME: Value variable as region state test 4
// RESULT: ACCEPT

/* DESCRIPTION: This test is equivalent to test_067, but does not restrict n to be non negative.
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
  requires Node(r, x, m) &*& r@(SET) &*& m >= 0 &*& (n = 0 ? true : Node(s, n, _)) &*& r != s;
  ensures Node(r, x, n) &*& r@(SET);
{
    [x + 1] := n;
}
