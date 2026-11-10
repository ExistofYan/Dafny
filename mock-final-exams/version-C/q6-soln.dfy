/* MOCK FINAL EXAM 2026 (Version C): Question 6.  -- SOLUTIONS

   8 marks in total

   This question is only for COMP6260 students.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: data invariants (like the sorted array of lecture 24),
   establishing / preserving an invariant, ghost functions that
   give the "abstract" view, fresh, old().

   A bounded STACK of integers is kept in one array a:
     a[0] holds the number of elements, n;
     the elements are a[1], ..., a[n], with the TOP at a[n];
     everything from a[n+1] up is unused junk.
*/

ghost predicate valid(a: array<int>)
  reads a
{
  a.Length > 0 && 0 <= a[0] < a.Length
}

ghost function elems(a: array<int>) : seq<int>
  reads a
  requires valid(a)
{
  a[1..a[0] + 1]
}

/* 6A.
   Implement empty, which makes a new, empty stack with room for
   cap elements.

   1 mark
*/
method empty(cap: nat) returns (a: array<int>)
  ensures fresh(a) && valid(a)
  ensures elems(a) == [] && a.Length == cap + 1
{
  a := new int[cap + 1];
  a[0] := 0;            // a fresh array's contents are unknown
}

/* 6B.
   Implement push.  (Specification given.)

   3 marks
*/
method push(a: array<int>, x: int)
  requires valid(a)
  requires |elems(a)| < a.Length - 1     // there is room
  modifies a
  ensures valid(a)
  ensures elems(a) == old(elems(a)) + [x]
{
  ghost var s := elems(a);
  var n := a[0];
  a[n + 1] := x;
  a[0] := n + 1;
  assert a[1..n + 1] == s;                     // the old elements are untouched
  assert a[1..n + 2] == a[1..n + 1] + [x];
}

/* 6C.
   Write the specification (requires / modifies / ensures) AND
   the body of pop, which removes and returns the top element.
   Your ensures must relate old(elems(a)), elems(a) and x.

   3 marks
*/
method pop(a: array<int>) returns (x: int)
  requires valid(a)
  requires |elems(a)| > 0
  modifies a
  ensures valid(a)
  ensures old(elems(a)) == elems(a) + [x]
{
  ghost var s := elems(a);
  var n := a[0];
  x := a[n];
  assert s[n - 1] == x;
  a[0] := n - 1;
  assert elems(a) == s[..n - 1];
  assert s == s[..n - 1] + [x];
}

/* 6D.
   In the comment: why is "there is room" a precondition of
   push rather than part of valid?

   1 mark
*/
/* valid describes EVERY legal stack, and a full stack is
   perfectly legal (you can still pop it).  Only push needs a
   free slot, so the caller of push must promise it.  If it
   were part of valid, a push that filled the last slot could
   not re-establish valid. */
