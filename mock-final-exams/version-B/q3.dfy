/* MOCK FINAL EXAM 2026 (Version B): Question 3.

   8 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   The functions append and reverse from core-list.dfy are
   particularly relevant in this question.

   Topics: accumulator-passing functions, GENERALISING the
   statement you prove (the keysA / hanoi_gen idea),
   append associativity.
*/

include "core-list.dfy"

function sumList(l: ilist) : int
{
  match l
  case Nil => 0
  case Cons(x, xs) => x + sumList(xs)
}

/* 3A.
   Define sumAcc(l, acc), a tail-recursive (accumulator)
   version of sumList: read sumAcc(l, acc) as "the sum of l,
   plus acc".  It must NOT call sumList.

   1 mark
*/
function sumAcc(l: ilist, acc: int) : int
{
  /* YOUR WORK GOES HERE */
}

/* 3B.
   State and prove the testing lemma that sumAcc on the list
   [1,2,3] with accumulator 0 is 6.

   1 mark
*/
/* YOUR WORK GOES HERE */

/* 3C.
   State and prove the GENERALISED lemma relating sumAcc(l, acc)
   to sumList(l), for every acc.  Make the inductive call
   explicit (do not rely on {} alone).

   2 marks
*/
/* YOUR WORK GOES HERE */

/* 3D.
   Using 3C, prove that sumAcc(l, 0) == sumList(l).

   1 mark
*/
lemma sumAcc_zero(l: ilist)
  ensures sumAcc(l, 0) == sumList(l)
{
  /* YOUR WORK GOES HERE */
}

/* 3E.
   Define revAcc(l, acc), the accumulator version of reverse
   (it should use only Cons, never append).

   1 mark
*/
function revAcc(l: ilist, acc: ilist) : ilist
{
  /* YOUR WORK GOES HERE */
}

/* 3F.
   State and prove that revAcc(l, acc) == append(reverse(l), acc).
   You will need to state and prove that append is associative.

   2 marks
*/
/* YOUR WORK GOES HERE */
