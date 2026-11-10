/* MOCK FINAL EXAM 2026 (Version B): Question 3.  -- SOLUTIONS

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
  match l
  case Nil => acc
  case Cons(x, xs) => sumAcc(xs, acc + x)
}

/* 3B.
   State and prove the testing lemma that sumAcc on the list
   [1,2,3] with accumulator 0 is 6.

   1 mark
*/
lemma sumAcc_test()
  ensures sumAcc(Cons(1, Cons(2, Cons(3, Nil))), 0) == 6 {}

/* 3C.
   State and prove the GENERALISED lemma relating sumAcc(l, acc)
   to sumList(l), for every acc.  Make the inductive call
   explicit (do not rely on {} alone).

   2 marks
*/
lemma sumAcc_sumList(l: ilist, acc: int)
  ensures sumAcc(l, acc) == sumList(l) + acc
{
  match l
  case Nil => {}
  case Cons(x, xs) => {
    sumAcc_sumList(xs, acc + x);   // note: a DIFFERENT accumulator
  }
}

/* 3D.
   Using 3C, prove that sumAcc(l, 0) == sumList(l).

   1 mark
*/
lemma sumAcc_zero(l: ilist)
  ensures sumAcc(l, 0) == sumList(l)
{
  sumAcc_sumList(l, 0);
}

/* 3E.
   Define revAcc(l, acc), the accumulator version of reverse
   (it should use only Cons, never append).

   1 mark
*/
function revAcc(l: ilist, acc: ilist) : ilist
{
  match l
  case Nil => acc
  case Cons(x, xs) => revAcc(xs, Cons(x, acc))
}

/* 3F.
   State and prove that revAcc(l, acc) == append(reverse(l), acc).
   You will need to state and prove that append is associative.

   2 marks
*/
lemma append_assoc<T>(a: list<T>, b: list<T>, c: list<T>)
  ensures append(append(a, b), c) == append(a, append(b, c))
{}

lemma revAcc_reverse(l: ilist, acc: ilist)
  ensures revAcc(l, acc) == append(reverse(l), acc)
{
  match l
  case Nil => {}
  case Cons(x, xs) => {
    revAcc_reverse(xs, Cons(x, acc));
    // append(append(reverse(xs), [x]), acc) == append(reverse(xs), Cons(x, acc))
    append_assoc(reverse(xs), Cons(x, Nil), acc);
  }
}
