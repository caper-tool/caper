// NAME: Disjunction test 2
// RESULT: ACCEPT

function foo(x, v, w)
  requires x |-> w;
  ensures x |-> v \/ x |-> w;
{
    if (v = w) {
        [x] := v;
    }
}
