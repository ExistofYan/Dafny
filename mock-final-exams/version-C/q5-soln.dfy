/* MOCK FINAL EXAM 2026 (Version C): Question 5.  -- SOLUTIONS

   10 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: sequence operations (indexing, slices, update,
   concatenation), loops over sequences, invariants that are
   "the postcondition cut off at i", forall AND exists in
   specs.
*/

/* 5A.
   Replace each ?? so that every assert verifies.

   1 mark
*/
method seqFacts()
{
  var s: seq<int> := [3, 1, 4, 1, 5];
  assert s[3..] == [1, 5];
  assert |s[1..4]| == 3;
  assert s[0 := 7] == [7, 1, 4, 1, 5];
  assert s[..2] + [9] == [3, 1, 9];
}

/* 5B.
   countUpTo(s, x, n) counts the x's among the first n elements
   of s.  Supply the body and loop invariants of countOcc.

   3 marks
*/
function countUpTo(s: seq<int>, x: int, n: nat) : nat
  requires n <= |s|
{
  if n == 0 then 0
  else countUpTo(s, x, n - 1) + (if s[n - 1] == x then 1 else 0)
}

method countOcc(s: seq<int>, x: int) returns (c: nat)
  ensures c == countUpTo(s, x, |s|)
{
  c := 0;
  var i: nat := 0;
  while i < |s|
    invariant i <= |s|
    invariant c == countUpTo(s, x, i)
  {
    if s[i] == x { c := c + 1; }
    i := i + 1;
  }
}

/* 5C.
   Implement isSorted by checking neighbouring pairs only.
   Supply the body and loop invariants.

   3 marks
*/
predicate sorted(s: seq<int>)
{
  forall p, q :: 0 <= p < q < |s| ==> s[p] <= s[q]
}

method isSorted(s: seq<int>) returns (b: bool)
  ensures b <==> sorted(s)
{
  if |s| <= 1 { return true; }
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant forall p, q :: 0 <= p < q < i ==> s[p] <= s[q]   // sorted(s[..i])
  {
    if s[i - 1] > s[i] { return false; }   // p = i-1, q = i is a counterexample
    i := i + 1;
  }
  return true;
}

/* 5D.
   Supply the body and loop invariants of findMax.  You need one
   invariant for EACH ensures clause, plus a counting invariant.

   3 marks
*/
method findMax(a: seq<int>) returns (m: int)
  requires |a| >= 1
  ensures forall j :: 0 <= j < |a| ==> a[j] <= m
  ensures exists j :: 0 <= j < |a| && a[j] == m
{
  var i := 1;
  m := a[0];
  while i < |a|
    invariant i <= |a|
    invariant forall j :: 0 <= j < i ==> a[j] <= m
    invariant exists j :: 0 <= j < i && a[j] == m
  {
    if a[i] >= m { m := a[i]; }
    i := i + 1;
  }
}
