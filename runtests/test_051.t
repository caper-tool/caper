// NAME: parenthesis peril 3
// RESULT: ACCEPT

// DESCRIPTION: this exercises a parser bug

function foo(x)
        requires x = y + 1;
        ensures x = (y + 1);
{
}

