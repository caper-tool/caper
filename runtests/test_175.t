// NAME: loop frame test 4
// RESULT: ACCEPT

// DESCRIPTION: Resources can frame around loops (but variables can be read)
function test(x)
  requires x |-> _;
  ensures x |-> _;
{
  [x] := 2;
  i := -7;
  do
  {
    if (i < 0) {
      i := x;
    }
    i := i - 1;
  }
  invariant true;
  while (i > 0);
  i := [x];
}
