module Ex3 {

  class Node {

    var val : nat
    var next : Node?

    // shouldn't this be a list ?
    ghost var footprint : set<Node>
    ghost var content : seq<nat> 

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
          this.content == [ this.val ]
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == [ this.val ] + this.next.content
          &&
          this.next.Valid()
    }

    constructor (v : nat) 
      ensures Valid() 
        && next == null && content == [ v ]
        && footprint == { this } 
        && val == v 
    {
      this.val := v; 
      this.next := null; 
      this.content := [ val ]; 
      this.footprint := { this };
    } 

    // add v at the start
    method add(v : nat) returns (r : Node)
      requires Valid()

      ensures r.Valid()
      ensures r.content == [v] + this.content
      ensures r.footprint == {r} + this.footprint
      ensures fresh(r)

      // not using ghost fields for spec
      ensures r.val == v;
    {
      r := new Node(v);
      r.next := this;
      r.content := [v] + this.content;
      r.footprint := {r} + this.footprint;
    }

    method mem(v : nat) returns (b : bool)
      requires Valid()
      ensures b == (v in this.content)
    {
      var cur := this;
      b := false;

      ghost var past := [];
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
          past := past + [ cur.val ];
        }

        cur := cur.next;
      }

      return;
    }

    method copy() returns (n : Node)
      requires Valid()

      decreases if this.next != null then footprint else {}

      ensures fresh(n.footprint)
      ensures n.Valid()
      ensures n.content == this.content
    {
      if this.next == null {
        n := new Node(this.val);
        return;
      } else {
        var other := this.next.copy();
        n := other.add(this.val);

        return;
      }
    }
  }

  // function Same(a: Node, b: Node): bool
  //   requires a.Valid()
  //   requires b.Valid()

  //   reads a, b
  //   reads a.footprint
  //   reads b.footprint

  //   decreases a.footprint
  // {
  //   a.val == b.val && (
  //     if a.next == null
  //       then b.next == null
  //       else
  //         if b.next == null
  //           then false
  //           else Same(a.next, b.next)
  //   )
  // }
  
}
