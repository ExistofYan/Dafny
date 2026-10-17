// var s : seq<int> := [1,2,3,4,5];//we can not define a variable out of method
const s: seq<int> := [1, 2, 3, 4, 5];
method test1(){
    var a : seq<int> := [1,2,3,4];
    var b : seq<bool> := [true,false,false,true];
    var c : seq<string> := ["java","python"];
    assert |a| == 4;//the length of a is |a|
    assert b[0] == true;
    assert c[|c|-1] == "python";//the last index is |c|-1
    //how to connect two sequence?
    var d := [10,20,30,40,50,60];
    var e := [70,80,90,100];
    var f := d + e;//using +
    assert f == [10,20,30,40,50,60,70,80,90,100];
    //judge if an element is in the sequence
    // assert 15 in f == false;//cannot do this
    assert 15 !in f;
    assert 100 in f;
    //change an element in the sequence
    var g := ["java","python","julia","c++","c#"];
    g := g[3 := "go"];//must have g := in the front!!!!!
    assert g  == ["java","python","julia","go","c#"];
    //sequence cannot directly change the original element but create a new sequence
    assert g[..|g|] == ["java","python","julia","go","c#"];

    var h := [1,2,3,4,5];
    var i := h;
    i := i[1 := 100];
    //the change of i does not change i
    assert i == [1,100,3,4,5];
    assert h == [1,2,3,4,5];
    var j := [5,4,3,2,1];
    //multiset() only cares the element itself and the times of occurance
    assert multiset(j) == multiset(h);

    assert forall x : nat | x < |j| :: j[x] < 100;
    assert exists x : nat | x < |j| :: j[x] == 5;

}

method findMax(s : seq<int>) returns (r : int)
{
    if |s| == 0 {return -1;}
    var max := s[0];
    var i := 0;
    while( i < |s|)
    invariant i <= |s|
    invariant forall x : nat | x < i :: s[x] <= max
    {
        if s[i] > max {max := s[i];}
        i := i + 1;
    }
    r := max;
}

method isRepeat(s : seq<int>) returns (r : bool)
{
    if |s| == 0 {r := false; return;}
    var i := 0;
    var num := 0;
    while(i < |s| - 1)
    invariant i <= |s|-1
    {
        var j := i + 1;
        num := s[i];
        while(j < |s|)
        invariant j <= |s|
        {
            if s[i] == s[j] {return true;}
            j := j + 1;
        }
        i := i + 1;
    }
    return false;
}
