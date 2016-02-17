// NAME: Consume non-zero perm 1
// RESULT: REJECT

function foo(x)
  requires r@FOO[1p];
  ensures r@FOO[0p];
{
  bar();
}

function bar()
  requires r@FOO[1p];
  ensures true;
{
}
