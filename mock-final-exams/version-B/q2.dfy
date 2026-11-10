/* MOCK FINAL EXAM 2026 (Version B): Question 2.

   8 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   The function member from core-list.dfy is particularly
   relevant in this question.

   Topics: lists used as sets, subset, case analysis with
   match inside proofs, the "what do we have / what do we
   want" table, auxiliary lemmas.
*/

include "core-list.dfy"

/* 2A.
   Define subset(A, B), true exactly when every element of
   list A is a member of list B.  Define it by recursion on A
   (do NOT use a forall).

   1 mark
*/
predicate subset(A: ilist, B: ilist)
{
  /* YOUR WORK GOES HERE */
}

/* 2B.
   State and prove the testing lemma that the list [1,2] is a
   subset of the list [2,3,1].

   1 mark
*/
/* YOUR WORK GOES HERE */

/* 2C.
   State and prove that if x is a member of A, and A is a
   subset of B, then x is a member of B.

   2 marks
*/
/* YOUR WORK GOES HERE */

/* 2D.
   State and prove that subset is transitive.  Your proof must
   use member_subset.

   2 marks
*/
/* YOUR WORK GOES HERE */

/* 2E.
   State and prove that subset is reflexive: subset(A, A).
   You will need to state, prove and use an auxiliary lemma:
   that if subset(A, B) then subset(A, Cons(x, B)).

   2 marks
*/
/* YOUR WORK GOES HERE */
