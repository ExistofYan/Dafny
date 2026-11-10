/* MOCK FINAL EXAM 2026 (Version B): Question 6.

   8 marks in total

   This question is only for COMP6260 students.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: sorted sequences, forall-statement proofs,
   binary search invariants (lo/hi windows).
*/

predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* 6A.
   Prove that appending an element that is at least as big as
   the last element of a sorted sequence keeps it sorted.
   Use a forall statement in your proof.

   2 marks
*/
lemma sorted_snoc(s: seq<int>, x: int)
  requires sorted(s)
  requires |s| == 0 || s[|s| - 1] <= x
  ensures sorted(s + [x])
{
  /* YOUR WORK GOES HERE */
}

/* 6B.
   Implement binary search.  search returns (found, idx): if
   found then a[idx] == x; if not found, x is nowhere in a.
   Supply the body, the loop invariants and a decreases clause.
   HINT: everything below lo is < x, everything from hi up is > x.

   6 marks
*/
method search(a: array<int>, x: int) returns (found: bool, idx: nat)
  requires sorted(a[..])
  ensures found ==> idx < a.Length && a[idx] == x
  ensures !found ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
  /* YOUR WORK GOES HERE */
}
