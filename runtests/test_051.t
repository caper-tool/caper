// NAME: Parenthesis peril 3
// RESULT: ACCEPT

function foo(x)
        requires x = y + 1;
        ensures x = (y + 1);
{
}

