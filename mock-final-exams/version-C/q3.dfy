/* MOCK FINAL EXAM 2026 (Version C): Question 3.

   8 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   The function member from core-list.dfy is particularly
   relevant in this question.

   Topics: exists and forall, witnesses with :|, ghost
   predicates, induction that uses quantified lemmas, proving
   an exists by exhibiting a witness.
*/

include "core-list.dfy"

ghost predicate divides(m: int, n: int)
{
  exists q: int :: q * m == n
}

function sumList(l: ilist) : int
{
  match l
  case Nil => 0
  case Cons(x, xs) => x + sumList(xs)
}

/* 3A.
   Prove that every m divides 0.

   1 mark
*/
lemma divides_zero(m: int)
  ensures divides(m, 0)
{
  /* YOUR WORK GOES HERE */
}

/* 3B.
   Prove that if m divides a and m divides b then m divides a + b.

   2 marks
*/
lemma divides_add(m: int, a: int, b: int)
  requires divides(m, a)
  requires divides(m, b)
  ensures divides(m, a + b)
{
  /* YOUR WORK GOES HERE */
}

/* 3C.
   Define allDivBy(m, l) RECURSIVELY: true when m divides every
   element of l.  Then state and prove that if allDivBy(m, l)
   then m divides sumList(l).

   2 marks
*/
ghost predicate allDivBy(m: int, l: ilist)
{
  /* YOUR WORK GOES HERE */
}

/* YOUR WORK GOES HERE */

/* 3D.
   (i)  State and prove that if allDivBy(m, l) and x is a member
        of l, then m divides x.                          (1 mark)
   (ii) Prove the lemma below: if NOT allDivBy(m, l) then there
        is a member of l that m does not divide.  You must give
        the witness explicitly.                          (2 marks)

   3 marks
*/
/* YOUR WORK GOES HERE */

lemma notAll_exists(m: int, l: ilist)
  requires !allDivBy(m, l)
  ensures exists x :: member(x, l) && !divides(m, x)
{
  /* YOUR WORK GOES HERE */
}
