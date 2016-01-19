// NAME: Fork test 3
// RESULT: ACCEPT

function forked(x)
  requires x |-> 0;
  ensures true;
{
  [x] := 1;
}

function forker()
  requires true;
  ensures true;
{
  x := alloc(2);
  [x] := 0;
  fork forked(x);
  y := [x+1];
}
