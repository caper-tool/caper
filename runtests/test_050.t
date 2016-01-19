// NAME: parenthesis peril 2
// RESULT: ACCEPT

// DESCRIPTION: this exercises a parser bug

function foo(x)
        requires x + 1 = y;
        ensures (x + 1) = y;
{
}

