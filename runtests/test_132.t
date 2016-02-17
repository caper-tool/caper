// NAME: Permission guard test 3
// RESULT: REJECT

function foo()
  requires r@GUARD[1p];
  ensures r@GUARD[v] &*& r@GUARD[v] &*& v = 0p;
{
}
