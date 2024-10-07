/**
    Helper functions and lemmas about conversion between set and seq.
 */

module SeqAndSet {
  lemma seq2setAdd(s: seq<nat>, k: nat)
  ensures seq2set(s + [k]) == seq2set(s) + {k}
  {
    if s == [] {
    } else {
      calc {
            seq2set(s + [k]);
          == { assert s == [s[0]] + s[1..]; }
            seq2set(([s[0]] + s[1..]) + [k]);
          == { assert ([s[0]] + s[1..]) + [k] == [s[0]] + (s[1..] + [k]);}
            seq2set([s[0]] + (s[1..] + [k]));
          ==
            seq2set(s) + {k};
      }
    }
  }

  lemma seq2seqEquiv(s: seq<nat>, c: set<nat>, k: nat)
    requires c == seq2set(s)

    ensures k in c <==> k in s
  {
    if k in c {
      seq2seqEquivAux(s, c, k);
      assert k in s;

    } else {
      if k in s {
          // contradiction
          seq2seqEquivAux2(s, c, k);
          assert k in c;
      } else {

      }
    }
  }

  lemma seq2seqEquivAux(s: seq<nat>, c: set<nat>, k: nat)
    requires c == seq2set(s)
    requires k in c
    
    ensures k in s
  {
    if s == [] {
    } else {
      if k == s[0] {
      } else {
        seq2seqEquivAux(s[1..], seq2set(s[1..]), k);
      }
    }

  }

  lemma seq2seqEquivAux2(s: seq<nat>, c: set<nat>, k: nat)
    requires c == seq2set(s)
    requires k in s
    
    ensures k in c
  {
    if s[0] == k {
    } else {
      seq2seqEquivAux2(s[1..], seq2set(s[1..]), k);
    }
  }

  lemma seq2setGood(s1: seq<nat>, s2: seq<nat>)
    requires s1 == s2
    ensures seq2set(s1) == seq2set(s2)
  {
  }

  /**
    Converts seq to set
   */
  function seq2set(s: seq<nat>): set<nat>
  {
    if s == [] then {} else {s[0]} + seq2set(s[1..])
  }
}