// NAME: loop frame test 2
// RESULT: ACCEPT

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
    return;
    i := i - 1;
  }
  i := [x];
}
