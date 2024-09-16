
module Ex3 {

  class Node {

    var val : nat
    var next : Node?

    ghost var footprint : set<Node>
    ghost var content : set<nat> 

    ghost function Valid() : bool 
      reads this, this.footprint 
      decreases footprint
    {
      this in this.footprint 
      &&
      if (this.next == null)
        then 
          this.footprint == { this }
          && 
          this.content == { this.val }
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == { this.val } + this.next.content
          &&
          this.next.Valid()
    }

    constructor (v : nat) 
    {
    }

    method add(v : nat) returns (r : Node)
    {
    }

    method mem(v : nat) returns (b : bool)
    {
  
    }

    method copy() returns (n : Node)
    {
    }

  
  }

  
}
