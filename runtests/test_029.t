// NAME: Equality test 3
// RESULT: REJECT

// DESCRIPTION: two assumed things should not be provably equal

function f()
        requires x = x &*& y = y;
        ensures x = y;
{
}

