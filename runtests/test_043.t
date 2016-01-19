// NAME: Fork test 1
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
  x := alloc(1);
  [x] := 0;
  fork forked(x);
}
