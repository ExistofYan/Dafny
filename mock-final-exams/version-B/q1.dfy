/* MOCK FINAL EXAM 2026 (Version B): Question 1.

   7 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: termination of recursive functions - decreases
   clauses, lexicographic (tuple) measures, mutual recursion;
   proving two facts at once by induction.
*/

/* 1A.
   sumRange(lo, hi) computes lo + (lo+1) + ... + (hi-1).
   Give it a decreases clause so that Dafny accepts it.
   Then state and prove the testing lemma that
   sumRange(3, 6) == 12.

   2 marks
*/
function sumRange(lo: int, hi: int) : int
  /* YOUR WORK GOES HERE */
  decreases hi - lo
{
  if lo >= hi then 0 else lo + sumRange(lo + 1, hi)
}
lemma test1()
ensures sumRange(3, 6) == 12
{}

/* YOUR WORK GOES HERE */

/* 1B.
   Give f a decreases clause so that Dafny accepts it.
   In the comment, explain in one sentence why your measure
   goes down in BOTH recursive calls.

   2 marks
*/
function f(m: nat, n: nat) : nat
  /* YOUR WORK GOES HERE */
  decreases m , n
{
  if m == 0 then n
  else if n == 0 then f(m - 1, 10)
  else f(m, n - 1)
}
/* YOUR WORK GOES HERE */

/* 1C.
   isEvenN and isOddN are defined by mutual recursion.  Give
   each a decreases clause so that Dafny accepts them.

   1 mark
*/
predicate isEvenN(n: nat)
  /* YOUR WORK GOES HERE */
  decreases n
{
  if n == 0 then true else isOddN(n - 1)
}

predicate isOddN(n: nat)
  /* YOUR WORK GOES HERE */
  decreases n
{
  if n == 0 then false else isEvenN(n - 1)
}

/* 1D.
   State and prove ONE lemma with TWO ensures clauses saying
     isEvenN(n) <==> n % 2 == 0
     isOddN(n)  <==> n % 2 == 1
   (Proving both at once gives you a strong enough induction
   hypothesis.)

   2 marks
*/
/* YOUR WORK GOES HERE */
lemma test2(n : nat)
decreases n
ensures isEvenN(n) <==> n % 2 == 0
ensures isOddN(n)  <==> n % 2 == 1
{}
