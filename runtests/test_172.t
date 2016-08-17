// NAME: loop frame test 1
// RESULT: ACCEPT

// DESCRIPTION: Resources can frame around loops
function test(x)
  requires x |-> _;
  ensures x |-> _;
{
  [x] := 2;
  i := 7;
  while (i > 0)
  invariant true;
  {
    i := i - 1;
  }
  i := [x];
}
