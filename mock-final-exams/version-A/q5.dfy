/* MOCK FINAL EXAM 2026 (Version A): Question 5.

   10 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: sequences and slices, quantifiers in specifications,
   early-exit loop guards, arrays, modifies, old(), the
   "part we have not touched yet" invariant.
*/

/* 5A.
   Define the predicate allPositive(s), true exactly when every
   element of s is strictly positive (use a forall).  Then
   state and prove that if allPositive(s) and s is non-empty,
   then allPositive(s[1..]).

   2 marks
*/
predicate allPositive(s: seq<int>)
{
  /* YOUR WORK GOES HERE */
  if |s| == 0 then true
  else (s[0] > 0) && allPositive(s[1..])
}

/* YOUR WORK GOES HERE */

/* 5B.
   Implement firstNeg, which returns the index of the first
   negative element of s, or |s| if there is none.  Supply
   the body and the loop invariants.

   2 marks
*/
method firstNeg(s: seq<int>) returns (idx: nat)
  ensures idx <= |s|
  ensures forall j :: 0 <= j < idx ==> s[j] >= 0
  ensures idx < |s| ==> s[idx] < 0
{
  /* YOUR WORK GOES HERE */
  if |s| == 0 {idx := |s|; return;}
  var i := 0;
    while(i < |s|)
    invariant i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] >= 0
    decreases |s| - i
    {
      if s[i] < 0 {idx := i; return;}
      i := i + 1;
    }
    idx := |s|;
}

/* 5C.
   Implement addToAll, which adds k to every element of the
   array a, IN PLACE.  Supply the body and the loop invariants.

   3 marks
*/
method addToAll(a: array<int>, k: int)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + k
{
  /* YOUR WORK GOES HERE */
  var i := 0;
  if a.Length == 0 {return;}
  while(i < a.Length)
  invariant i<=a.Length
  invariant forall j :: 0 <= j < i ==> a[j] == old(a[j]) + k
  invariant forall z :: i <= z < a.Length ==> a[z] == old(a[z])
  {
    a[i] := a[i] + k;
    i := i + 1;
  }
}

/* 5D.
   Implement minIndex, which returns the index of a smallest
   element of the (non-empty) array a.  Supply the body and
   the loop invariants.  Note: no modifies clause is needed -
   why not?  (Answer in a comment; no marks, but think about it.)

   3 marks
*/
method minIndex(a: array<int>) returns (m: nat)//每出现一个变量，如果感觉没东西写了，就写这个变量
  requires a.Length > 0
  ensures m < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[m] <= a[i]
{
  /* YOUR WORK GOES HERE */
  var i := 1;
  var min := a[0];
  var index := 0;
  while(i < a.Length)
  invariant 1 <= i <= a.Length
  invariant 0 <= index < i
  invariant min == a[index]
  invariant forall j :: 0 <= j < i ==> a[index] <= a[j]
  {
    if min > a[i] {min := a[i];index := i;}
    i := i + 1;
  }
  m := index;
}
