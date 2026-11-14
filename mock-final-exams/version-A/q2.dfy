/* MOCK FINAL EXAM 2026 (Version A): Question 2.

   8 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   The functions member, append and reverse from core-list.dfy
   are particularly relevant in this question.

   Topics: list recursion, testing lemmas, structural induction,
   iff (<==>) lemmas, calling an auxiliary lemma inside a proof.
*/

include "core-list.dfy"

/* 2A.
   Define count(x, l), the number of times x occurs in l.

   1 mark
*/
function count(x: int, l: ilist) : nat
{
  /* YOUR WORK GOES HERE */
  match l
  case Nil => 0
  case Cons(h,t) => if x == h then 1 + count(x,t) else count(x,t)
}

/* 2B.
   State and prove the testing lemma that 1 occurs twice in the
   list containing 1, 2, 1, 3 (in that order).

   1 mark
*/
/* YOUR WORK GOES HERE */
lemma test1()
ensures count(1,Cons(1,Cons(2,Cons(1,Cons(3,Nil))))) == 2
{}

/* 2C.
   State and prove that counting x in append(l1, l2) gives the
   sum of the counts of x in l1 and in l2.

   2 marks
*/
/* YOUR WORK GOES HERE */
lemma count_append(l1 : ilist , l2 :ilist , x : int)
ensures count(x,append(l1,l2)) == count(x,l1) + count(x,l2)
{}

/* 2D.
   State and prove that x is a member of l if and only if
   the count of x in l is greater than zero.

   2 marks
*/
/* YOUR WORK GOES HERE */
lemma test3(x : int , l : ilist)
ensures count(x,l) > 0 ==> member(x,l)
{}

/* 2E.
   State and prove that reversing a list does not change the
   count of any element.  You will need to call count_append
   in your proof.

   2 marks
*/
/* YOUR WORK GOES HERE */
lemma test4(x : int , l : ilist)
ensures count(x,l) == count(x,reverse(l))
{
   match l case Nil => {}
   case Cons(h,t) => {
      test4(x,t);
      assert l == append(Cons(h,Nil),t);
      count_append(Cons(h,Nil),t,x);
      assert count(x,l) == count(x,Cons(h,Nil)) + count(x,t);
      assert reverse(l) == append(reverse(t),Cons(h,Nil));
      count_append(reverse(t),Cons(h,Nil),x);
      assert count(x,reverse(l)) == count(x,reverse(t)) + count(x,Cons(h,Nil));
   }
}