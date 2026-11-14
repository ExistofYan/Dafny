/* MOCK FINAL EXAM 2026 (Version B): Question 5.

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
  /* YOUR WORK GOES HERE */
  reads a
{
  /* YOUR WORK GOES HERE */
  forall i : nat , j : nat | i < j < a.Length :: a[i] <= a[j]
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
  /* YOUR WORK GOES HERE */
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
  /* YOUR WORK GOES HERE */
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
  /* YOUR WORK GOES HERE */
{
  /* YOUR WORK GOES HERE */
}
