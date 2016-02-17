// NAME: Produced permission non-zero 1
// RESULT: ACCEPT

function foo(x)
  requires r@FOO[p];
  ensures p != 0p;
{
}

