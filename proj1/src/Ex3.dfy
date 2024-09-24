
module Ex3 {

  class Node {

    var val : nat
    var next : Node?

    // shouldn't this be a list ?
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
      ensures Valid() 
        && next == null && content == { v }
        && footprint == { this } 
        && val == v 
    {
      this.val := v; 
      this.next := null; 
      this.content := { val }; 
      this.footprint := { this };
    } 

    method add(v : nat) returns (r : Node)
      requires Valid()
      ensures r.Valid()
      ensures r.content == {v} + this.content
      ensures r.footprint == {r} + this.footprint
      ensures fresh(r)
    {
      r := new Node(v);
      r.next := this;
      r.content := {v} + this.content;
      r.footprint := {r} + this.footprint;
    }

    method mem(v : nat) returns (b : bool)
      requires Valid()
      ensures b == (v in this.content)
    {
      var cur := this;
      b := false;

      ghost var past := {};
      while (cur != null)
        decreases if cur != null then cur.footprint else {}
        invariant cur != null ==> this.content == past + cur.content
        invariant cur == null ==> this.content == past
        invariant v !in past
        invariant cur != null ==> cur.Valid()
      {
        if (cur.val == v)
        {
          b := true;
          return;
        } else {
          past := past + { cur.val };
        }

        cur := cur.next;
      }

      return;
    }

    method copy() returns (n : Node)
      requires Valid()
      ensures fresh(n.footprint)
      // ensures Same(n, this)
    {
    }
  }

  function Same(a: Node?, b: Node?): bool
    requires a != null ==> a.Valid()
    requires b != null ==> b.Valid()

    reads a, b
    reads if a != null then a.footprint else {}
    reads if b != null then b.footprint else {}

    decreases if a != null then a.footprint else {}
  {
    if a == null
      then b == null
      else if b == null
        then false
        else a.val == b.val && Same(a.next, b.next)
  }
  
}
