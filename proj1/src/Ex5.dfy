include "Ex3.dfy"

module Ex5 {
  
  import Ex3=Ex3

  class Set {
    var tbl : array<bool>  
    var list : Ex3.Node?

    ghost function Valid() : bool 
    {

    }
      
    constructor (size : nat) 
    {
    }


    method mem (v : nat) returns (b : bool)
    {
    }
    
    method add (v : nat) 
    {
    }

    method union(s : Set) returns (r : Set)
    {
    }

    method inter(s : Set) returns (r : Set)
    {
    }

  }

}