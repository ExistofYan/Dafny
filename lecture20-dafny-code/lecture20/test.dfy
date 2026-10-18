method test(){
    var a : array<int> := new int[10];
    a[0] := 10;
    a[1] := 20;
    a[2] := 30;
    a[3] := 40;
    a[4] := 50;
    assert a.Length == 10;
    a[0] := 0;
    assert a[..5] == [0,20,30,40,50];

    var b := a;
    b[0] := 100;
    // the change of b will change the array of a
    assert a[..5] == [100,20,30,40,50];

    // == compare the reference. which is the same as java array
    assert a == b;

    //how to compare their content -> convert them into sequence
    assert a[..] == b[..];

    //modify a -> means the method is allowed to modify a with the same reference

    assert multiset([1,2,3]) == multiset([3,2,1]);
}

method example(a: array<int>, b: array<int>)
  requires a.Length > 1 && b.Length > 1
  modifies a
{
    if a == b {
        b[1] := 0;
    }
}
predicate sorted(a: array<int>)
  reads a
{
    forall i, j ::
      0 <= i < j < a.Length ==> a[i] <= a[j]
}
method increase(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures a[0] == old(a[0]) + 10//old(a[0])
{
    a[0] := a[0] + 10;
}