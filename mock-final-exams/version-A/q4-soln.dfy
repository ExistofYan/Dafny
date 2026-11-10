/* MOCK FINAL EXAM 2026 (Version A): Question 4.  -- SOLUTIONS

   9 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: methods with specifications, while loops, loop
   invariants (counting + computing), the three verifier
   complaints, "answer to what is left" invariants, decreases.
*/

function power(b: int, n: nat) : int
{
  if n == 0 then 1 else b * power(b, n - 1)
}

/* 4A.
   State and prove the testing lemma that 3 to the power 4 is 81.

   1 mark
*/
lemma power_test()
  ensures power(3, 4) == 81 {}

/* 4B.
   Implement powerLoop using a while loop (no recursion and no
   call to power in the body), with the loop invariants needed
   for Dafny to accept it.

   3 marks
*/
method powerLoop(b: int, n: nat) returns (r: int)
  ensures r == power(b, n)
{
  var i: nat := 0;
  r := 1;
  while i < n
    invariant i <= n                // counting
    invariant r == power(b, i)      // computing
  {
    r := b * r;
    i := i + 1;
  }
}

/* 4C.
   The method below does not verify.

   (i)  In the comment, say WHICH of the three questions Dafny
        asks about a loop invariant fails (holds on entry? /
        maintained by the body? / gives the postcondition at
        the end?), and why.
   (ii) Fix the method by ADDING ONE invariant only.

   2 marks
*/
/* (i) The postcondition fails ("a postcondition could not be
       proved on this return path").  At the end we know only
       i <= n and !(i < n), so i == n, but nothing at all about s.
   (ii) Add the computing invariant  s == i * i.               */
method sumOdds(n: nat) returns (s: nat)
  ensures s == n * n
{
  var i: nat := 0;
  s := 0;
  while i < n
    invariant i <= n
    invariant s == i * i
  {
    s := s + 2 * i + 1;
    i := i + 1;
  }
}

/* 4D.
   digits(n) is the number of decimal digits in n.  Complete the
   loop in digitsLoop with an invariant and a decreases clause so
   that Dafny accepts the method.
   HINT: d counts digits already removed; digits(n) counts the
   digits that are left.

   3 marks
*/
function digits(n: nat) : nat
{
  if n < 10 then 1 else 1 + digits(n / 10)
}

method digitsLoop(n0: nat) returns (d: nat)
  ensures d == digits(n0)
{
  var n := n0;
  d := 1;
  while n >= 10
    invariant d + digits(n) == digits(n0) + 1
    decreases n
  {
    n := n / 10;
    d := d + 1;
  }
}
