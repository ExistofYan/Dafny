/* MOCK FINAL EXAM 2026 (Version C): Question 4.

   9 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: writing method specifications, method opacity
   (callers only see the ensures), logical accumulators
   (found <==> exists ...), break, decreases with an
   expression that is not just a variable.
*/

/* 4A.
   Write BOTH the specification (two ensures clauses: m is at
   least each argument, and m is one of the arguments) AND
   the body of maxOf3.

   2 marks
*/
method maxOf3(x: int, y: int, z: int) returns (m: int)
  /* YOUR WORK GOES HERE */
{
  /* YOUR WORK GOES HERE */
}

/* 4B.
   useTriple fails to verify even though triple obviously
   returns 12 when given 4.
   (i)  Explain why in the comment.
   (ii) Fix it by changing triple's specification ONLY.

   2 marks
*/
/* YOUR WORK GOES HERE */
method triple(x: int) returns (r: int)
  /* YOUR WORK GOES HERE */
{
  r := 3 * x;
}

method useTriple()
{
  var t := triple(4);
  assert t == 12;
}

/* 4C.
   Implement hasNegative with a loop that STOPS EARLY (use
   break) as soon as it finds a negative value.  Supply the
   body and the loop invariants.

   3 marks
*/
method hasNegative(f: nat -> int, n: nat) returns (found: bool)
  ensures found <==> exists i :: 0 <= i < n && f(i) < 0
{
  /* YOUR WORK GOES HERE */
}

/* 4D.
   Give the loop a decreases clause so that Dafny can prove it
   terminates.  Note that k itself goes UP.

   2 marks
*/
method squareAbove(n: nat) returns (k: nat)
  ensures k * k >= n
{
  k := 0;
  while k * k < n
    /* YOUR WORK GOES HERE */
  {
    k := k + 1;
  }
}
