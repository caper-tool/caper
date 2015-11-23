// NAME: Equality test 1
// RESULT: REJECT

// DESCRIPTION: a thing should be equal to itself

function f()
        requires x = x;
        ensures false;
{
}

