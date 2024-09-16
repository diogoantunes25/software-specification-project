method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
 {
  var i := 0; 
  b := true; 

  while (i < arr.Length) 
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length) 
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
}




method noRepetitionsLinear(arr : array<nat>) returns (b: bool) 
{

}
