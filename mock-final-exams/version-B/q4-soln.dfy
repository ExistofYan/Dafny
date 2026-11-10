/* MOCK FINAL EXAM 2026 (Version B): Question 4.  -- SOLUTIONS

   9 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: loops that compute recursive functions, two
   changing variables (fib-style), "answer to what is left"
   invariants, invariant-on-entry failures, decreases *.
*/

function lucas(n: nat) : int
{
  if n == 0 then 2 else if n == 1 then 1 else lucas(n - 1) + lucas(n - 2)
}

/* 4A.
   Supply the loop invariants for lucasLoop.

   3 marks
*/
method lucasLoop(n: nat) returns (a: int)
  ensures a == lucas(n)
{
  var b: int := 1;
  var i: nat := 0;
  a := 2;
  while i < n
    invariant i <= n
    invariant a == lucas(i)
    invariant b == lucas(i + 1)
  {
    a, b, i := b, a + b, i + 1;
  }
}

/* 4B.
   sumDown adds up n0 + (n0-1) + ... + 1 by counting DOWN.
   Supply the loop invariant and decreases clause.
   HINT: s is the part already added; sumTo(n) is what is left.

   3 marks
*/
function sumTo(n: nat) : nat
{
  if n == 0 then 0 else n + sumTo(n - 1)
}

method sumDown(n0: nat) returns (s: nat)
  ensures s == sumTo(n0)
{
  var n := n0;
  s := 0;
  while n > 0
    invariant s + sumTo(n) == sumTo(n0)
    decreases n
  {
    s := s + n;
    n := n - 1;
  }
}

/* 4C.
   The method below does not verify.
   (i)  Which of the three invariant questions fails, and for
        which value(s) of n?
   (ii) Give TWO different one-line fixes (one that changes the
        specification, one that changes the code).

   2 marks
*/
method startsAtOne(n: nat) returns (i: nat)
  ensures i == n
{
  i := 0;     // Fix 2 applied here so this solution file verifies
  while i < n
    invariant i <= n
  {
    i := i + 1;
  }
}
/* (i)  "This loop invariant might not hold on entry": when
        n == 0 we start with i == 1 and 1 <= 0 is false.
   (ii) Fix 1 (spec): add   requires n >= 1.
        Fix 2 (code): initialise   i := 0;   instead of 1.    */

/* 4D.
   Nobody knows whether the Collatz loop below terminates for
   every n0.  Add the annotations needed for Dafny to accept the
   method WITHOUT proving termination, and say in the comment
   what the ensures clause then guarantees.

   1 mark
*/
method collatz(n0: nat) returns (n: nat)
  requires n0 > 0
  ensures n == 1
  decreases *
{
  n := n0;
  while n > 1
    invariant n > 0
    decreases *
  {
    if n % 2 == 0 { n := n / 2; } else { n := 3 * n + 1; }
  }
}
/* Partial correctness only: IF the method returns, then n == 1.
   It promises nothing if the loop runs forever. */
