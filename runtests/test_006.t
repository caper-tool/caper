// NAME: recursive identity
// RESULT: ACCEPT

// DESCRIPTION: a recursive identity function on nats

function id(x)
        requires x >= 0;
        ensures ret = x;
{
        if (x = 0) {
                return 0;
        } else {
                y := id(x - 1);
                return (y + 1);
        }
}

