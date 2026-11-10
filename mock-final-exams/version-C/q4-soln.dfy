/* MOCK FINAL EXAM 2026 (Version C): Question 4.  -- SOLUTIONS

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
  ensures m >= x && m >= y && m >= z
  ensures m == x || m == y || m == z
{
  m := x;
  if y > m { m := y; }
  if z > m { m := z; }
}

/* 4B.
   useTriple fails to verify even though triple obviously
   returns 12 when given 4.
   (i)  Explain why in the comment.
   (ii) Fix it by changing triple's specification ONLY.

   2 marks
*/
/* (i) Methods are opaque: a caller only knows what the
       ensures clauses say, never the body.  triple had no
       ensures, so useTriple knows nothing about t.          */
method triple(x: int) returns (r: int)
  ensures r == 3 * x
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
  found := false;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant !found
    invariant forall j :: 0 <= j < i ==> f(j) >= 0
  {
    if f(i) < 0 {
      found := true;
      break;            // invariant not needed after break: i is the witness
    }
    i := i + 1;
  }
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
    decreases n - k * k
  {
    k := k + 1;
  }
}
