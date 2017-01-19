/*
  Adaptation of atomic reference count to Caper -- alternate version

  This version does not depend on abductive reasoning.
*/

// Assumptions: an abstract predicate object with functions for
// creating and destroying it

predicate object();

function create()
  requires true;
  ensures object();
{ create();}

function destroy()
  requires object();
  ensures true;
{}

// Atomic reference count region

region ARC(r,c,x) {
  guards |arc|;
  interpretation {
    n > 0 | n : object() &*& r@arc|-1-n| &*& c |-> n;
    0 : r@arc|-1|;
  }
  actions {
    n > 0, m >= 0 | : n ~> m;
  }
}

function init()
  requires true;
  ensures ARC(r,ret,x,_) &*& r@arc|1|;
{
  create();
  c := alloc(1);
  [c] := 1;
  return c;
}

function clone(c)
  requires ARC(r,c,x,_) &*& r@arc|1|;
  ensures ARC(r,c,x,_) &*& r@arc|2|;
{
  do {
    cnt := [c];
    b := CAS(c,cnt,cnt+1);
  }
    invariant b = 0 ? ARC(r,c,x,_) &*& r@arc|1| : ARC(r,c,x,_) &*& r@arc|2|;
  while (b = 0);
}

function drop(c)
  requires ARC(r,c,x,_) &*& r@arc|1|;
  ensures true;
{
  do {
    cnt := [c];
    assert (cnt = 1 ? true : true);
    b := CAS(c,cnt,cnt-1);
  }
    invariant b = 0 ? ARC(r,c,x,_) &*& r@arc|1| : (cnt = 1 ? object() : true);
  while (b = 0);
  if (cnt = 1) {
    destroy();
  }
}
