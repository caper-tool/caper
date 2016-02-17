// NAME: Permission guard test 2
// RESULT: REJECT

function foo()
  requires r@GUARD[1p];
  ensures r@GUARD[v] &*& r@GUARD[v];
{
}
