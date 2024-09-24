datatype uop = Neg 
datatype bop = Plus | Minus 

datatype aexpr =
  Var(seq<nat>)
  | Val(nat)
  | UnOp(uop, aexpr)
  | BinOp(bop, aexpr, aexpr)
 
datatype code = 
  | VarCode(seq<nat>)  
  | ValCode(nat)       
  | UnOpCode(uop)      
  | BinOpCode(bop)     

function Serialize(a : aexpr) : seq<code> 
{
  match a {
    case Var(s) => [ VarCode(s) ]
    case Val(i) => [ ValCode(i) ]
    case UnOp(op, a1) => Serialize(a1) + [ UnOpCode(op) ]
    case BinOp(op, a1, a2) => Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
  }
}

method Main() {
    var result := Deserialize(Serialize(BinOp(Minus, BinOp(Plus, Val(1), Val(2)), BinOp(Minus, Val(1), Val(3)))));
    print result;
}

/*
  Ex1.1
*/
function Deserialize(cs : seq<code>) : seq<aexpr> 
{
  if cs == [] then [] else DeserializeRec(cs, [])  
}

function DeserializeRec(cs: seq<code>, exprs: seq<aexpr>): seq<aexpr>
{
  if cs == []
  then exprs
  else DeserializeRec(cs[1..], DeserializeSingle(cs[0], exprs))
}

function DeserializeSingle(c: code, exprs: seq<aexpr>): seq<aexpr>
{
  match c {
    case VarCode(s) => [Var(s)] + exprs
    case ValCode(i) => [Val(i)] + exprs
    case UnOpCode(uop) => if |exprs| < 1 then [] else [UnOp(uop, exprs[0])] + exprs[1..]
    case BinOpCode(bop) => if |exprs| < 2 then [] else [BinOp(bop, exprs[0], exprs[1])] + exprs[2..]
  }
}

/*
  Ex1.2
*/
lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [ e ]
{
  match e {
    // I was expecting the base cases to require 0 stuff
    case Var(s) => {
        // Does this need to be in calculational style ?
        assert(Deserialize(Serialize(e)) == DeserializeRec([VarCode(s)], []));
    }
    case Val(i) => {
        // Does this need to be in calculational style ?
        assert(Deserialize(Serialize(e)) == DeserializeRec([ValCode(i)], []));
    }
    case UnOp(op, a1) => calc {
          Deserialize(Serialize(e));
        ==  { assert Serialize(e) == Serialize(e) + []; }
          Deserialize(Serialize(e) + []);
        == { DeserializeSegments(UnOp(op,a1), [], []); }
          [UnOp(op, a1)];
    }
    case BinOp(op, a1, a2) => calc {
          Deserialize(Serialize(e));
        ==  { assert Serialize(e) == Serialize(e) + []; }
          Deserialize(Serialize(e) + []);
        == { DeserializeSegments(BinOp(op,a1,a2), [], []); }
          [BinOp(op, a1, a2)];
    }
  }
}

lemma DeserializeSegments(a: aexpr, ops: seq<code>, l: seq<aexpr>)
  ensures DeserializeRec(Serialize(a) + ops, l) == DeserializeRec(ops, [a] + l)
{
  match a {
    case Var(s) => {}
    case Val(i) => {}
    case UnOp(op, a1) => calc {
        DeserializeRec(Serialize(UnOp(op, a1)) + ops, l);
      ==
        DeserializeRec(Serialize(a1) + [UnOpCode(op)] + ops, l);
      == {assert Serialize(a1) + [UnOpCode(op)] + ops == Serialize(a1) + ([UnOpCode(op)] + ops); }
        DeserializeRec(Serialize(a1) + ([UnOpCode(op)] + ops), l);
      == { DeserializeSegments(a1, [UnOpCode(op)] + ops, l); }
        DeserializeRec([UnOpCode(op)] + ops, [a1] + l);
      ==
        DeserializeRec(ops, [a] + l);
    }
    case BinOp(op, a1, a2) => calc {
        DeserializeRec(Serialize(BinOp(op, a1, a2)) + ops, l);
      ==
        DeserializeRec(Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ] + ops, l);
      == {assert Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ] + ops == Serialize(a2) + (Serialize(a1) + [ BinOpCode(op) ] + ops); }
        DeserializeRec(Serialize(a2) + (Serialize(a1) + [ BinOpCode(op) ] + ops), l);
      ==
        DeserializeRec(Serialize(a1) + [ BinOpCode(op) ] + ops, [a2] + l);
      == {assert Serialize(a1) + [ BinOpCode(op) ] + ops == Serialize(a1) + ([ BinOpCode(op) ] + ops); }
        DeserializeRec(Serialize(a1) + ([ BinOpCode(op) ] + ops), [a2] + l);
      == { DeserializeSegments(a1, [ BinOpCode(op) ] + ops, [a2] + l); }
        DeserializeRec([ BinOpCode(op) ] + ops, [a1] + ([a2] + l));
      == {assert [a1, a2] + l == [a1] + ([a2] + l); }
        DeserializeRec([ BinOpCode(op) ] + ops, [a1, a2] + l);
      ==
        DeserializeRec(ops, [BinOp(op, a1, a2)] + l);
    }
  }
}


/*
  Ex1.3
*/
function SerializeCodes(cs : seq<code>) : seq<nat> 
{
  if cs == [] then [] else SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..])
}

function SerializeSingleCode(cs : code) : seq<nat> 
{
  match cs {
    case VarCode(s) => [0, |s|] + s
    case ValCode(i) => [1, i]
    case UnOpCode(uop) => [2]
    case BinOpCode(bop) => match bop {
      case Plus => [3, 0]
      case Minus => [3, 1]
    }
  }
}

function DeserializeCodes(ints : seq<nat>) : seq<code> {
  DeserializeCodesRec(ints, []) 
}

function DeserializeCodesRec(ints : seq<nat>, cs: seq<code>) : seq<code>

{
  if ints == []
  then cs
  else match ints[0] {
    case 0 => 
      if |ints| < 2 then []
      else if |ints[2..]| < ints[1] then []
      else DeserializeCodesRec(ints[2..][(ints[1])..], [VarCode(ints[2..][..(ints[1])])] + cs)
    case 1 =>
      if |ints| < 2 then []
      else DeserializeCodesRec(ints[2..], [ValCode(ints[1])] + cs)
    case 2 => DeserializeCodesRec(ints[1..], [UnOpCode(Neg)] + cs)
    case 3 => if |ints| < 2
      then []
      else match ints[1] {
        case 0 => DeserializeCodesRec(ints[2..], [BinOpCode(Plus)] + cs)
        case 1 => DeserializeCodesRec(ints[2..], [BinOpCode(Minus)] + cs)
        case _ => []
      }
    case _ => [] // invalid serialization
  }
}

// /*
//   Ex1.4
// */
lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
  if cs == [] { }
  else {
    calc {
        DeserializeCodes(SerializeCodes(cs));
      ==
        DeserializeCodes(SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..]));
      ==
        DeserializeCodesRec(SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..]), []);
      == 
        DeserializeCodes(SerializeSingleCode(cs[0])) + DeserializeCodes(SerializeCodes(cs[1..]));
      == { DeserializeSingleCodeProperty(cs[0]); }
        [cs[0]] + DeserializeCodes(SerializeCodes(cs[1..]));
      ==
        [cs[0]] + cs[1..];
      ==
        cs;
    }
  }
}

lemma DeserializeSingleCodeProperty(c : code)
  ensures DeserializeCodes(SerializeSingleCode(c)) == [c]
{
  match c {
    case VarCode(s) => {
      var ints := [0, |s|] + s;
      calc {
          DeserializeCodes(SerializeSingleCode(VarCode(s)));
        ==
          DeserializeCodesRec([0, |s|] + s, []);
        == 
          DeserializeCodesRec(ints, []);
        ==
          DeserializeCodesRec(ints[2..][(ints[1])..], [VarCode(ints[2..][..(ints[1])])] + []);
        ==
          DeserializeCodesRec([], [VarCode(ints[2..][..(ints[1])])] + []);
        ==
          DeserializeCodesRec([], [VarCode(s[..(ints[1])])] + []);
        ==
          DeserializeCodesRec([], [VarCode(s[..(|s|)])] + []);
        == { assert s[..|s|] == s; }
          DeserializeCodesRec([], [VarCode(s)] + []);
        ==
          [c];
      }
    }
    case ValCode(i) => calc {
          DeserializeCodes(SerializeSingleCode(ValCode(i)));
        ==
          DeserializeCodes([1, i]);
        ==
          DeserializeCodes([1, i]);
        ==
          DeserializeCodesRec([], [ValCode(i)] + []);
        ==
          [c];
    }
    case UnOpCode(uop) => calc {
          DeserializeCodes(SerializeSingleCode(UnOpCode(uop)));
        ==
          DeserializeCodesRec([], [UnOpCode(Neg)] + []);
        == {assert uop == Neg;}
          [c];
    }
    // Can i use the match inside a calc ?
    case BinOpCode(bop) => match bop {
      case Plus => calc {
          DeserializeCodes(SerializeSingleCode(BinOpCode(bop)));
        == { assert Plus == bop; } // why is this needed?
          DeserializeCodesRec([], [BinOpCode(Plus)] + []);
        ==
          [c];
      }
      case Minus => calc {
          DeserializeCodes(SerializeSingleCode(BinOpCode(bop)));
        ==
          DeserializeCodesRec([], [BinOpCode(Minus)] + []);
        ==
          [c];
      }
    }
  }
}

// /*
//   Ex1.5
// */
function FullSerialize(e : aexpr) : seq<nat> {
  SerializeCodes(Serialize(e))
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
  Deserialize(DeserializeCodes(nats))
}

// /*
//   Ex1.6
// */
lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
  calc {
      FullDeserealize(FullSerialize(e));
    ==
      Deserialize(DeserializeCodes(SerializeCodes(Serialize(e))));
    == { DeserializeCodesProperty(Serialize(e)); }
      Deserialize((Serialize(e)));
    == { DeserializeProperty(e); }
      [ e ];
  }
}