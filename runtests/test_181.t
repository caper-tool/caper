// NAME: Zero permission trouble
// RESULT: REJECT

// DESCRIPTION: Caper can end up with the guards F * G[0p] internally
//     which previously it would have considered inconsistent.

region Ra(x) {
  guards %G + F;
  interpretation {
    0 : true;
  }
  actions {}
}


function bar()
  requires true;
  ensures false;
{
  great();
}

function great()
  requires Ra(r,0) &*& r@G[p] &*& p = 1p;
  ensures r@F;
{
}
