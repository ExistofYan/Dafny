/* MOCK FINAL EXAM 2026 (Version B): Question 5.  -- SOLUTIONS

   10 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: arrays, reads, modifies, fresh, old(), frame
   conditions ("I did not touch anything else"), multisets.
*/

/* 5A.
   Define the predicate sortedArr(a), true exactly when the
   array a is sorted in non-decreasing order.  (Don't forget
   what a predicate needs in order to look inside an array.)

   1 mark
*/
predicate sortedArr(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

/* 5B.
   Implement copyArray, which returns a NEW array with the same
   contents as a.  Supply the body and the loop invariants.
   (Why is there no modifies clause?  Think about it.)

   3 marks
*/
method copyArray(a: array<int>) returns (b: array<int>)
  ensures fresh(b)
  ensures b.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[i]
{
  // b is fresh (allocated here), so it needs no modifies clause.
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> b[j] == a[j]
  {
    b[i] := a[i];
    i := i + 1;
  }
}

/* 5C.
   Implement zeroNegatives, which replaces every negative
   element of a by 0 and leaves the others alone.  Supply the
   body and the loop invariants.

   3 marks
*/
method zeroNegatives(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==>
            (old(a[i]) < 0 ==> a[i] == 0) && (old(a[i]) >= 0 ==> a[i] == old(a[i]))
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==>
                (old(a[j]) < 0 ==> a[j] == 0) && (old(a[j]) >= 0 ==> a[j] == old(a[j]))
    invariant forall j :: i <= j < a.Length ==> a[j] == old(a[j])
  {
    if a[i] < 0 { a[i] := 0; }
    i := i + 1;
  }
}

/* 5D.
   Write the FULL specification (requires/modifies/ensures) and
   the body of swap, which exchanges a[i] and a[j].  Your ensures
   clauses must say:
     - what a[i] and a[j] now hold,
     - that every OTHER element is unchanged, and
     - that the multiset of elements is unchanged.

   3 marks
*/
method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  a[i], a[j] := a[j], a[i];
}
