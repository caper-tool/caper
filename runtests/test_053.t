// NAME: parenthesis peril 4
// RESULT: ACCEPT

// DESCRIPTION: this exercises a parser bug

function foo(x)
        requires x + 1 = y + 1;
        ensures ((x + 1) = (y + 1));
{
}

