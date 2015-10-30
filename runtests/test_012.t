// NAME: parenthesis peril
// RESULT: ACCEPT

// DESCRIPTION: this exercises a parser bug

function foo(x)
        requires x + 1 |-> 3;
        ensures (x + 1) |-> 3;
{
}

