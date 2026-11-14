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
  match l
  case Nil => 0
  case Cons(x, xs) => x + sumAcc(xs,acc + x)
}

/* 3B.
   State and prove the testing lemma that sumAcc on the list
   [1,2,3] with accumulator 0 is 6.

   1 mark
*/
/* YOUR WORK GOES HERE */
lemma sumAcc_accumulator()
ensures sumAcc(Cons(1,Cons(2,Cons(3,Nil))),0) == 6
{}
/* 3C.
   State and prove the GENERALISED lemma relating sumAcc(l, acc)
   to sumList(l), for every acc.  Make the inductive call
   explicit (do not rely on {} alone).

   2 marks
*/
/* YOUR WORK GOES HERE */
lemma sumAcc_sumList(l: ilist, acc: int)
ensures sumAcc(l, acc) == sumList(l)
{}
/* 3D.
   Using 3C, prove that sumAcc(l, 0) == sumList(l).

   1 mark
*/
lemma sumAcc_zero(l: ilist)
  ensures sumAcc(l, 0) == sumList(l)
{
  /* YOUR WORK GOES HERE */
  sumAcc_sumList(l,0);
}

/* 3E.
   Define revAcc(l, acc), the accumulator version of reverse
   (it should use only Cons, never append).

   1 mark
*/
function revAcc(l: ilist, acc: ilist) : ilist
{
  /* YOUR WORK GOES HERE */
  match l
  case Nil => acc
  case Cons(h,t) => revAcc(t,Cons(h,acc))
}

/* 3F.
   State and prove that revAcc(l, acc) == append(reverse(l), acc).
   You will need to state and prove that append is associative.

   2 marks
*/
/* YOUR WORK GOES HERE */
lemma test1(l: ilist, acc: ilist)
ensures revAcc(l, acc) == append(reverse(l), acc)
{
   match l 
   case Nil => {
      assert revAcc(l, acc) == acc;
      assert reverse(l) == Nil;
   }
   case Cons(h,t) => {
      test1(t,acc);
      assert reverse(l) == append(reverse(t),Cons(h,Nil));
      assert revAcc(l,acc) == revAcc(t,Cons(h,acc));
      assert append(reverse(l), acc) == append(append(reverse(t),Cons(h,Nil)),acc);
      append_associative(reverse(t),Cons(h,Nil),acc);
      assert append(reverse(l), acc) == append(reverse(t),append(Cons(h,Nil),acc));
   }
}
lemma append_associative(l1 : ilist , l2 : ilist , l3 :ilist)
ensures append(append(l1,l2),l3) == append(l1,append(l2,l3))
{}
