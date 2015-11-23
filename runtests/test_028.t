// NAME: Equality test 2
// RESULT: ACCEPT

// DESCRIPTION: A thing should not be disequal to itself

function f()
        requires x != x;
        ensures false;
{
}

