include "Ex3.dfy"
include "SeqAndSet.dfy"

module Ex4 {
  import Ex3=Ex3
  import SAS=SeqAndSet

  class Set {
    // Should not have duplicates
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list
    {
      if (this.list == null)
        then 
          footprint == {}
          &&
          content == {}
        else 
          footprint == list.footprint
          &&
          content == SAS.seq2set(list.content)
          &&
          list.Valid()
    }

    constructor () 
      ensures Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }

    /**
      Checks if the current set contains the value v 
      Complexity: O(n)
     */
    method mem (v : nat) returns (b : bool)
      requires this.Valid()
      ensures b == (v in this.content)
    {
      if this.list == null {
        b := false;
        return;
      } else {
        b := this.list.mem(v);

        // to understand that the mem check extends to this content
        SAS.seq2seqEquiv(this.list.content, this.content, v);
        return;
      }
    }

    /**
      Adds v to the current set 
      Complexity: O(n)
     */
    method add (v : nat) 
      requires this.Valid()
      modifies this

      ensures this.Valid()
      ensures this.content == old(this.content) + {v}
    {
      // O(n)
      var b := this.mem(v);

      // O(1)
      if !b {
        if this.list == null {
          this.list := new Ex3.Node(v);
          this.footprint := {this.list};
          this.content := {v};
        } else {
          this.list := this.list.add(v);
          this.footprint := this.list.footprint;
          this.content := {v} + this.content;
        }
      }
    }

    /**
      Union of the current set and the set s given as input 
      Complexity: O(|s| * |this|)
     */
    method union(s : Set) returns (r : Set)
      requires s.Valid()
      requires this.Valid()

      ensures fresh(r)
      ensures r.Valid()
      ensures r.content == s.content + this.content
    {
      r := new Set();

      // O(|s|)
      if s.list != null {
        r.list := s.list.copy();
        r.footprint := r.list.footprint;
        r.content := SAS.seq2set(r.list.content);
      }

      assert r.content == s.content;

      // O(|s| * |this|)
      var cur := this.list;

      ghost var seen : seq<nat> := [];
      while cur != null
        invariant cur != null ==> cur.Valid()
        invariant r.Valid()
        invariant cur != null ==> this.list.content == seen + cur.content
        invariant cur == null ==> this.content == SAS.seq2set(seen)
        invariant r.content == s.content + SAS.seq2set(seen)

        decreases if cur != null then cur.footprint else {}
      {
        ghost var oldR := r.content;
        r.add(cur.val);
        assert r.content == oldR + {cur.val};

        ghost var oldSeen := seen;
        seen := seen + [cur.val];
        SAS.seq2seqEquiv(seen, SAS.seq2set(seen), cur.val);
        SAS.seq2setAdd(oldSeen, cur.val);

        cur := cur.next;
      }

    }

    /**
      Intersection of the current set and the set s given as input 
      Complexity: O(|s| * |this|)
     */
    method inter(s : Set) returns (r : Set)
      requires s.Valid() 
      requires this.Valid() 

      ensures fresh(r)
      ensures r.Valid()
      ensures r.content == s.content * this.content
    {
      r := new Set();

      // O(|s| * |this|)
      var cur := this.list;
      ghost var seen : seq<nat> := [];
      while cur != null
        invariant cur != null ==> cur.Valid()
        invariant r.Valid()
        invariant cur != null ==> this.list.content == seen + cur.content
        invariant cur == null ==> this.content == SAS.seq2set(seen)
        invariant r.content == s.content * SAS.seq2set(seen)
        decreases if cur != null then cur.footprint else {}
      {
        var inIntersection := s.mem(cur.val);
        if inIntersection {
          ghost var oldR := r.content;
          r.add(cur.val);
          assert r.content == oldR + {cur.val};
        }

        ghost var oldSeen := seen;
        seen := seen + [cur.val];
        SAS.seq2seqEquiv(seen, SAS.seq2set(seen), cur.val);
        SAS.seq2setAdd(oldSeen, cur.val);

        cur := cur.next;
      }

    }
  }
}
