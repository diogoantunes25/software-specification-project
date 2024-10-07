function noRepsF(v: seq<nat>): bool
{
  forall i, j :: 0 <= i < |v| && 0 <= j < |v| ==> i != j ==> v[i] != v[j]
}

method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  ensures b == noRepsF(arr[..])
 {
  var i := 0; 
  b := true; 

  while (i < arr.Length) 
      invariant 0 <= i <= arr.Length
      invariant forall j, k :: 0 <= k < i && 0 <= j < arr.Length ==>
                                    j != k ==> arr[j] != arr[k]
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length) 
      invariant 0 <= j <= arr.Length
      invariant forall k :: 0 <= k < j && k != i ==> arr[i] != arr[k]
    {
      var u := arr[j]; 
      if ((j != i) && (u == v)) {
        b := false; 
        return; 
      }
      j := j+1;
    }
    i := i+1; 
  }

  assert forall j, k :: 0 <= k < arr.Length && 0 <= j < arr.Length ==> j != k ==> arr[j] != arr[k];
}

method noRepetitionsLinear(arr : array<nat>) returns (b: bool) 
  ensures b == noRepsF(arr[..])
{
  var max := 0;
  var i := 0;
  while i < arr.Length
    invariant max >= 0
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> max >= arr[j]
  {
    if arr[i] > max {
      max := arr[i];
    }
    i := i + 1;
  }

  // allocation + initialization assumed to be constant-time
  var present := new bool[max+1](_ => false);

  i := 0;
  while i < arr.Length
      invariant 0 <= i <= arr.Length
      invariant forall j :: 0 <= j < i ==> present[arr[j]] == true
      invariant forall v :: (0 <= v <= max && present[v]) ==> exists k :: (0 <= k < i && arr[k] == v)
      invariant forall j, k :: 0 <= j < k < i ==> arr[j] != arr[k]
  {
    if present[arr[i]] {
      assert exists k :: 0 <= k < i && arr[k] == arr[i];
      b := false;
      return;
    }

    assert forall k :: 0 <= k < i ==> arr[k] != arr[i];
    present[arr[i]] := true;
    i := i + 1;
  }

  b := true;
  return;
}
