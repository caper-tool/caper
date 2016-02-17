// NAME: Produced permission non-zero 2
// RESULT: ACCEPT

function foo(x)
  requires r@FOO[0p];
  ensures false;
{
}

