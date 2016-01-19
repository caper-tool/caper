// Increment

function incr(x)
  requires x |-> v0;
  ensures x |-> v0 + 1;
{
    do 
        invariant x |-> vi &*& (b != 0 ? vi = (v0 + 1) : vi = v0)
    {
        v := [x];
        b := CAS(x, v, v + 1);
    } while (b = 0);
    return v;
}

function incr2(x)
  requires x |-> v0;
  ensures x |-> v0 + 2;
{
    incr(x);
    incr(x);
}

function parallelIncr(x, y)
  requires x |-> v0 &*& y |-> w0;
  ensures x |-> v0 + 1 &*& y |-> w0 + 1;
{
	incr(x);
	incr(y);
}

function read(x)
  requires x |-> v0;
  ensures x |-> v1 &*& ret = v1;
{
    v := [x];
    return v;
}
