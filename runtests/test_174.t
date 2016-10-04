// NAME: loop frame test 3
// RESULT: REJECT

// DESCRIPTION: Resources can frame around loops (even with returns)
function test(x)
  requires x |-> _;
  ensures x |-> _;
{
  [x] := 2;
  i := 7;
  while (i > 0)
  invariant true;
  {
    [x] := 7;
    i := i - 1;
  }
  i := [x];
}
