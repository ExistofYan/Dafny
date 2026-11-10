/* MOCK FINAL EXAM 2026: EXTRA CHALLENGE QUESTIONS.  -- SOLUTIONS

   Not part of any one paper.  These are the hardest loop
   patterns from lectures 19-23 (three-region arrays, sorting,
   nested loops).  Do them AFTER Versions A, B and C.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.
*/

/* X1. Reverse an array in place.
   The array has THREE regions during the loop: done at the
   front, done at the back, untouched in the middle.  Supply
   the loop invariants.
*/
method reverse(a: array<int>)
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
{
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: a.Length - i <= k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: i <= k < a.Length - i ==> a[k] == old(a[k])
  {
    a[i], a[a.Length - 1 - i] := a[a.Length - 1 - i], a[i];
    i := i + 1;
  }
}

/* X2. Selection sort.
   sel is given.  Supply the outer loop's invariants for
   sel_srt.  HINT: "the first p are sorted" is not enough -
   what must hold between the finished prefix and the rest?
*/
ghost predicate sorted(a: seq<int>)
{ forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j] }

ghost predicate parted(s: seq<int>, p: nat)
{ forall i, j :: 0 <= i < p <= j < |s| ==> s[i] <= s[j] }

method sel(a: array<int>, p: nat) returns (q: nat)
  requires p < a.Length
  ensures p <= q < a.Length
  ensures forall i :: p <= i < a.Length ==> a[q] <= a[i]
{
  q := p;
  var k := p + 1;
  while k < a.Length
    invariant k <= a.Length
    invariant p <= q < k
    invariant forall i :: p <= i < k ==> a[q] <= a[i]
  {
    if a[k] < a[q] { q := k; }
    k := k + 1;
  }
}

method sel_srt(a: array<int>)
  modifies a
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var p: nat := 0;
  while p < a.Length
    invariant p <= a.Length
    invariant sorted(a[0..p])
    invariant parted(a[..], p)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var q := sel(a, p);
    a[p], a[q] := a[q], a[p];
    p := p + 1;
  }
}

/* X3. Duplicate-free check with NESTED loops.
   Supply the invariants of both loops.  Remember: the inner
   loop is opaque to the outer one, so the inner loop must
   also carry what the outer loop needs.
*/
predicate dup_free(a: seq<int>)
{ forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j] }

method nodup(a: seq<int>) returns (b: bool)
  ensures b <==> dup_free(a)
{
  if |a| == 0 { return true; }
  var m: nat := 0;
  while m < |a| - 1
    invariant m < |a|
    invariant forall i: nat :: i < m ==> a[i] !in a[i + 1..]
  {
    var n: nat := m + 1;
    while n < |a|
      invariant m < n <= |a|
      invariant forall i: nat :: i < m ==> a[i] !in a[i + 1..]
      invariant forall j: nat :: m < j < n ==> a[j] != a[m]
    {
      if a[n] == a[m] { return false; }
      n := n + 1;
    }
    m := m + 1;
  }
  return true;
}
