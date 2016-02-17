// NAME: Permission guard test 2
// RESULT: ACCEPT

function foo()
  requires r@GUARD[1p];
  ensures r@GUARD[v] &*& r@GUARD[v];
{
}
