include "Ex3.dfy"
include "Ex4.dfy"

module Ex5 {
  
  import Ex3=Ex3

  // Just for theorems about sets and seqs
  import Ex4=Ex4

  class Set {
    var tbl : array<bool>  
    var list : Ex3.Node?

    ghost var size: nat
    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list, this.tbl
    {
      // Only values between 0 and size are allowed
      (forall v :: v in content ==> 0 <= v < tbl.Length) &&

      // The array keeps track of membership correctly
      (forall k :: 0 <= k < tbl.Length ==> tbl[k] == (k in this.content)) &&

      size == tbl.Length - 1 &&

      // Footprint, content, and list are correct
      (if list == null
        then
          footprint == {} &&
          content == {}
        else
          footprint == this.list.footprint &&
          content == Ex4.seq2set(this.list.content) &&
          list.Valid()
      )
    }
      
    constructor (size : nat) 
      ensures Valid() && this.content == {} && this.footprint == {} && this.size == size
    {
      // size + 1 because elements might be equal to size
      this.tbl := new bool[size+1](_ => false);
      this.list := null;

      this.size := size;
      this.footprint := {};
      this.content := {};
    }

    // O(1)
    method mem (v : nat) returns (b : bool)
      requires this.Valid()
      ensures b == (v in this.content)
    {
      if v >= tbl.Length {
        b := false;
        return;
      } else {
        b := tbl[v];
        return;
      }
    }
    
    // O(1)
    method add (v : nat) 
      requires 0 <= v <= size
      requires this.Valid()

      modifies this, this.tbl, this.list

      ensures this.Valid()
      ensures this.size == old(this.size)
      ensures this.content == old(this.content) + {v}
      ensures this.tbl == old(this.tbl)
    {
      // to avoid duplicates
      var b := this.mem(v);

      if !b {
        tbl[v] := true;

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

    // O(n)
    method union(s : Set) returns (r : Set)
      requires s.Valid()
      requires this.Valid()

      ensures fresh(r)
      ensures r.Valid()
      // ensures r.content == s.content + this.content
      ensures r.content == s.content
    {
      var mSize := max(this.tbl.Length-1, s.tbl.Length-1);

      r := new Set(mSize);

      assert r.size >= this.size;
      assert r.size >= s.size;

      // O(|s| * |s|)
      var cur := s.list;

      ghost var seen : seq<nat> := [];

      while cur != null
        invariant cur != null ==> cur.Valid()

        invariant r.Valid()
        invariant r.size >= s.size

        invariant cur != null ==> s.list.content == seen + cur.content
        // invariant cur == null ==> s.content == Ex4.seq2set(seen)
        // invariant r.content == Ex4.seq2set(seen)

        decreases if cur != null then cur.footprint else {}
      {
        // ghost var oldR := r.content;
        // Ex4.seq2seqEquiv(s.list.content, s.content, cur.val);

        Ex4.seq2seqEquiv(s.list.content, s.content, cur.val);
        assert 0 <= cur.val <= s.size;
        r.add(cur.val);
        // assert r.content == oldR + {cur.val};

        ghost var oldSeen := seen;
        seen := seen + [cur.val];
        Ex4.seq2seqEquiv(seen, Ex4.seq2set(seen), cur.val);
        Ex4.seq2setAdd(oldSeen, cur.val);

        cur := cur.next;
      }

      assert r.Valid();

      // assert r.content == s.content;

      // // O(|s| * |this|)
      // cur := this.list;

      // seen := [];
      // while cur != null
      //   invariant cur != null ==> cur.Valid()
      //   invariant r.Valid()
      //   invariant r.size >= this.size
      //   invariant cur != null ==> this.list.content == seen + cur.content
      //   invariant cur == null ==> this.content == Ex4.seq2set(seen)
      //   invariant r.content == s.content + Ex4.seq2set(seen)

      //   decreases if cur != null then cur.footprint else {}
      // {
      //   ghost var oldR := r.content;
      //   assert cur.val in cur.content;
      //   assert cur.val in this.list.content;
      //   Ex4.seq2seqEquiv(this.list.content, this.content, cur.val);
      //   assert cur.val in this.content;
      //   assert r.Valid();
      //   assert 0 <= cur.val < this.tbl.Length;
      //   assert 0 <= cur.val < r.tbl.Length;
      //   assert 0 <= cur.val <= r.size;
      //   r.add(cur.val);
      //   assert r.content == oldR + {cur.val};

      //   ghost var oldSeen := seen;
      //   seen := seen + [cur.val];
      //   Ex4.seq2seqEquiv(seen, Ex4.seq2set(seen), cur.val);
      //   Ex4.seq2setAdd(oldSeen, cur.val);

      //   cur := cur.next;
      // }
    }

    // O(n)
    method inter(s : Set) returns (r : Set)
      requires s.Valid() 
      requires this.Valid() 

      ensures r.Valid()
      ensures r.content == s.content * this.content
    {
    }

  }

  function maxF(a: nat, b: nat): nat
  {
    if a > b then a else b
  }

  method max(a: nat, b: nat) returns (c: nat)
    ensures c == maxF(a, b)
  {
    if a > b {
      c := a;
    } else {
      c := b;
    }
  }

}