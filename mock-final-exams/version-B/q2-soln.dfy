/* MOCK FINAL EXAM 2026 (Version B): Question 2.  -- SOLUTIONS

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
  match A
  case Nil => true
  case Cons(x, xs) => member(x, B) && subset(xs, B)
}

/* 2B.
   State and prove the testing lemma that the list [1,2] is a
   subset of the list [2,3,1].

   1 mark
*/
lemma subset_test()
  ensures subset(Cons(1, Cons(2, Nil)), Cons(2, Cons(3, Cons(1, Nil)))) {}

/* 2C.
   State and prove that if x is a member of A, and A is a
   subset of B, then x is a member of B.

   2 marks
*/
lemma member_subset(x: int, A: ilist, B: ilist)
  requires member(x, A)
  requires subset(A, B)
  ensures member(x, B)
{}

/* 2D.
   State and prove that subset is transitive.  Your proof must
   use member_subset.

   2 marks
*/
lemma subset_trans(A: ilist, B: ilist, C: ilist)
  requires subset(A, B)
  requires subset(B, C)
  ensures subset(A, C)
{
  match A
  case Nil => {}
  case Cons(h, t) => {
    // have: member(h, B), subset(t, B), subset(B, C)
    // want: member(h, C), subset(t, C)
    member_subset(h, B, C);
    subset_trans(t, B, C);
  }
}

/* 2E.
   State and prove that subset is reflexive: subset(A, A).
   You will need to state, prove and use an auxiliary lemma:
   that if subset(A, B) then subset(A, Cons(x, B)).

   2 marks
*/
lemma subset_cons(A: ilist, B: ilist, x: int)
  requires subset(A, B)
  ensures subset(A, Cons(x, B))
{}

lemma subset_refl(A: ilist)
  ensures subset(A, A)
{
  match A
  case Nil => {}
  case Cons(h, t) => {
    subset_refl(t);           // subset(t, t)
    subset_cons(t, t, h);     // subset(t, Cons(h, t)) == subset(t, A)
  }
}
