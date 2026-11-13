/* MOCK FINAL EXAM 2026 (Version A): Question 4.

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
/* YOUR WORK GOES HERE */
lemma test1()
ensures power(3,4) == 81
{}

/* 4B.
   Implement powerLoop using a while loop (no recursion and no
   call to power in the body), with the loop invariants needed
   for Dafny to accept it.

   3 marks
*/
method powerLoop(b: int, n: nat) returns (r: int)
  ensures r == power(b, n)
{
  /* YOUR WORK GOES HERE */
  var x , y := b , n;
  var sum := 1;
  if y == 0 { r := 1;}
  while(y > 0)
  invariant y >= 0
  invariant sum == power(x,n-y)
  {
    sum := sum * x;
    y := y - 1;
  }
  r := sum;
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
/* YOUR WORK GOES HERE */
method sumOdds(n: nat) returns (s: nat)
  ensures s == n * n
{
  var i: nat := 0;
  s := 0;
  while i < n
    invariant i <= n
    /* YOUR WORK GOES HERE */
    // invariant if i % 2 == 0 then s % 2 == 0 else s % 2 == 1 //  1 3 5 7 9 -> 1 4 9 16 25
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
  if n < 10 then 1 else 1 + digits(n / 10)//123 -> 1 + 1 + 1 = 3
}

method digitsLoop(n0: nat) returns (d: nat)
  ensures d == digits(n0)
{
  var n := n0;
  d := 1;
  while n >= 10
    /* YOUR WORK GOES HERE */
    invariant n >= 0
    invariant d == digits(n0) - digits(n) + 1
    decreases n
  {
    n := n / 10;
    d := d + 1;
  }
}
