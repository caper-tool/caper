// NAME: Consume non-zero perm 3
// RESULT: REJECT

function foo(x)
  requires r@FOO[1p];
  ensures r@FOO[p] &*& p = 0p;
{
  bar();
}

function bar()
  requires r@FOO[q];
  ensures true;
{
}
