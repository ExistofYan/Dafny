/* MOCK FINAL EXAM 2026 (Version A): Question 6.  -- SOLUTIONS

   8 marks in total

   This question is only for COMP6260 students.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: exists, extracting witnesses with :|, ghost
   predicates, multisets, a partitioning loop with several
   regions (like the Dutch national flag).
*/

ghost predicate isEven(n: int)
{
  exists k: int :: n == 2 * k
}

/* 6A.
   Prove that the sum of two even numbers is even.

   2 marks
*/
lemma even_add(m: int, n: int)
  requires isEven(m)
  requires isEven(n)
  ensures isEven(m + n)
{
  var a :| m == 2 * a;
  var b :| n == 2 * b;
  assert m + n == 2 * (a + b);
}

/* 6B.
   Prove that an even number times any number is even.

   2 marks
*/
lemma even_mul(m: int, n: int)
  requires isEven(m)
  ensures isEven(m * n)
{
  var a :| m == 2 * a;
  assert m * n == 2 * (a * n);
}

/* 6C.
   Implement partitionEvens, which rearranges a so that all the
   even numbers come first, followed by all the odd numbers, and
   returns p, the index where the odd numbers start.  Use a
   single loop with two indices lo and hi (lo moves up, hi
   moves down).  Supply the body, the loop invariants and a
   decreases clause.

   4 marks
*/
method partitionEvens(a: array<int>) returns (p: nat)
  modifies a
  ensures p <= a.Length
  ensures forall i :: 0 <= i < p ==> a[i] % 2 == 0
  ensures forall i :: p <= i < a.Length ==> a[i] % 2 != 0
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] % 2 == 0        // evens
    invariant forall i :: hi <= i < a.Length ==> a[i] % 2 != 0 // odds
    invariant multiset(a[..]) == multiset(old(a[..]))
    // nothing is said about lo..hi: it is the unknown region
    decreases hi - lo
  {
    if a[lo] % 2 == 0 {
      lo := lo + 1;
    } else {
      hi := hi - 1;
      a[lo], a[hi] := a[hi], a[lo];
    }
  }
  p := lo;
}
