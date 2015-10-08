// NAME: recursive identity (broken)
// RESULT: REJECT

// DESCRIPTION: a broken recursive identity function

function id(x)
        requires x >= 0;
        ensures ret = x;
{
        if (x = 0) {
                return 0;
        } else {
                y := id(x - 1);
                return y;
        }
}

