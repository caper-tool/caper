// NAME: Consume non-zero perm 2
// RESULT: REJECT

function foo(x)
  requires true;
  ensures r@FOO[0p];
{
}

