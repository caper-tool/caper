// NAME: loop frame test 5
// RESULT: REJECT

// DESCRIPTION: Resources can frame around loops (but variables can be read but not written)
function test(x)
  requires x |-> _;
  ensures x |-> _;
{
  [x] := 2;
  i := -7;
  do
  {
    j := x + i;
    i := i - 1;
    x := j - i;
  }
  invariant true;
  while (i > 0);
  i := [x];
}
