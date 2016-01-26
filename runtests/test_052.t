// NAME: Parenthesis peril 4
// RESULT: ACCEPT

function foo(x)
        requires (x) + (1) = (y) + (1);
        ensures ((x) + (1)) = ((y) + (1));
{
}

