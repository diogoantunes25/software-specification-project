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

function DeserializeCodes(ints : seq<nat>) : seq<code>
{
  if ints == []
  then []
  else match ints[0] {
    case 0 => 
      if |ints| < 2 then []
      else if |ints[2..]| < ints[1] then []
      else [VarCode(ints[2..][..(ints[1])])] + DeserializeCodes(ints[2..][(ints[1])..])
    case 1 =>
      if |ints| < 2 then []
      else [ValCode(ints[1])] + DeserializeCodes(ints[2..])
    case 2 => [UnOpCode(Neg)] + DeserializeCodes(ints[1..])
    case 3 => if |ints| < 2
      then []
      else match ints[1] {
        case 0 => [BinOpCode(Plus)] + DeserializeCodes(ints[2..])
        case 1 => [BinOpCode(Minus)] + DeserializeCodes(ints[2..])
        case _ => []
      }
    case _ => [] // invalid serialization
  }
}

/*
  Ex1.4
*/
lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
  if cs == [] { }
  else {
    calc {
        DeserializeCodes(SerializeCodes(cs));
      ==
        DeserializeCodes(SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..]));
      == { DeserializeCodeSingleProperty(cs[0], cs[1..]); }
        [cs[0]] + DeserializeCodes(SerializeCodes(cs[1..]));
      == // induction hypothesis
        [cs[0]] + cs[1..];
      ==
        cs;
    }
  }
}

lemma DeserializeCodeSingleProperty(c: code, cs: seq<code>)
  ensures DeserializeCodes(SerializeSingleCode(c) + SerializeCodes(cs)) == [c] + DeserializeCodes(SerializeCodes(cs))
{
  match c {
    case VarCode(s) => {
      var ints := [0, |s|] + s + SerializeCodes(cs);
      calc {
          DeserializeCodes(SerializeSingleCode(VarCode(s)) + SerializeCodes(cs));
        ==
          DeserializeCodes([0, |s|] + s + SerializeCodes(cs));
        ==
          DeserializeCodes(ints);
        ==
          [VarCode(ints[2..][..(ints[1])])] + DeserializeCodes(ints[2..][(ints[1])..]);
        ==
          [VarCode(s)] + DeserializeCodes(ints[2..][(ints[1])..]);
        ==
          [VarCode(s)] + DeserializeCodes(SerializeCodes(cs));
        ==
          [c] + DeserializeCodes(SerializeCodes(cs));
      }
    }
    case ValCode(i) => calc {
          DeserializeCodes(SerializeSingleCode(ValCode(i)) + SerializeCodes(cs));
        ==
          DeserializeCodes([1, i] + SerializeCodes(cs));
        ==
          [ValCode(i)] + DeserializeCodes(SerializeCodes(cs));
        ==
          [c] + DeserializeCodes(SerializeCodes(cs));
    }
    case UnOpCode(uop) => calc {
          DeserializeCodes(SerializeSingleCode(UnOpCode(uop)) + SerializeCodes(cs));
        ==
          DeserializeCodes([2] + SerializeCodes(cs));
        ==
          [UnOpCode(Neg)] + DeserializeCodes(SerializeCodes(cs));
        == { assert uop == Neg; }
          [UnOpCode(uop)] + DeserializeCodes(SerializeCodes(cs));
    }
    // Can i use the match inside a calc ?
    case BinOpCode(bop) => match bop {
      case Plus => calc {
          DeserializeCodes(SerializeSingleCode(BinOpCode(bop)) + SerializeCodes(cs));
        == { assert bop == Plus; }
          DeserializeCodes(SerializeSingleCode(BinOpCode(Plus)) + SerializeCodes(cs));
        ==
          DeserializeCodes([3, 0] + SerializeCodes(cs));
        ==
          [BinOpCode(Plus)] + DeserializeCodes(SerializeCodes(cs));
        == { assert bop == Plus; }
          [BinOpCode(bop)] + DeserializeCodes(SerializeCodes(cs));
      }
      case Minus => calc {
          DeserializeCodes(SerializeSingleCode(BinOpCode(bop)) + SerializeCodes(cs));
        == { assert bop == Minus; }
          DeserializeCodes(SerializeSingleCode(BinOpCode(Minus)) + SerializeCodes(cs));
        ==
          DeserializeCodes([3, 0] + SerializeCodes(cs));
        ==
          [BinOpCode(Minus)] + DeserializeCodes(SerializeCodes(cs));
        == { assert bop == Minus; }
          [BinOpCode(bop)] + DeserializeCodes(SerializeCodes(cs));
      }
    }
  }
}

// lemma DeserializeCodePreservation(c : code, cs: seq<code>, l: seq<code>)
//   ensures DeserializeCodesRec(SerializeSingleCode(c) + SerializeCodes(cs), l) ==
//           [c] + DeserializeCodesRec(SerializeCodes(cs), l)
// {
//   if cs == [] {
//     calc {
//         DeserializeCodesRec(SerializeSingleCode(c) + SerializeCodes([]), l);
//       == { assert SerializeCodes([]) == []; }
//         DeserializeCodesRec(SerializeSingleCode(c) + [], l);
//       == { assert SerializeSingleCode(c) + [] == SerializeSingleCode(c); }
//         DeserializeCodesRec(SerializeSingleCode(c), l);
//       == { DeserializeSingleCodePropertyStrong(c, l); }
//         [c] + l;
//     }
//   } else {
//     calc {
//         DeserializeCodesRec(SerializeSingleCode(c) + SerializeCodes(cs), l);
//       ==
//         DeserializeCodesRec(SerializeSingleCode(c) + SerializeCodes(cs), l);
//       ==
//         DeserializeCodesRec(SerializeSingleCode(c) + (SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..])), l);
//       ==
//         DeserializeCodesRec(SerializeSingleCode(c) + (SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..])), l);
//       ==
//         DeserializeCodesRec(SerializeSingleCode(c) + (SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..])), l);
//       == { DeserializeCodeExchange(c, (SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..])), l); }
//         DeserializeCodesRec(SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..]), [c] + l);
//       ==
//         DeserializeCodesRec(SerializeSingleCode(cs[0]) + SerializeCodes(cs[1..]), [c] + l);
//       ==
//         [c] + DeserializeCodesRec(SerializeCodes(cs), l);
//     }
//   }
// }

// lemma DeserializeCodeExchange(c: code, o: seq<nat>, l: seq<code>)
//   ensures DeserializeCodesRec(SerializeSingleCode(c) + o, l) ==
//           DeserializeCodesRec(o, l + [c])
// {
//   match c {
//     case VarCode(s) => {
//       var ints := [0, |s|] + s + o;
//       calc {
//           DeserializeCodesRec(SerializeSingleCode(VarCode(s)) + o, l);
//         ==
//           DeserializeCodesRec(ints, l);
//         == 
//           DeserializeCodesRec(ints[2..][(ints[1])..], l + [VarCode(ints[2..][..(ints[1])])]);
//         ==
//           DeserializeCodesRec(o, l + [VarCode(ints[2..][..(ints[1])])]);
//         == { assert ints[2..][..(ints[1])] == s[..(|s|)]; }
//           DeserializeCodesRec(o, l + [VarCode(s[..(|s|)])]);
//         == { assert s[..|s|] == s; }
//           DeserializeCodesRec(o, l + [VarCode(s)]);
//       }
//     }
//     case ValCode(i) => calc {
//           DeserializeCodesRec(SerializeSingleCode(ValCode(i)) + o, l);
//         ==
//           DeserializeCodesRec(o, l + [ValCode(i)]);
//     }
//     case UnOpCode(uop) => calc {
//           DeserializeCodesRec(SerializeSingleCode(UnOpCode(uop)) + o, l);
//         == {assert uop == Neg;}
//           DeserializeCodesRec(o, l + [UnOpCode(uop)]);
//     }
//     // Can i use the match inside a calc ?
//     case BinOpCode(bop) => match bop {
//       // why can't dafny do this
//       case Plus => calc { }
//       case Minus => calc { }
//     }
//   }

// }

// lemma DeserializeSingleCodePropertyStrong(c : code, l: seq<code>)
//   ensures DeserializeCodesRec(SerializeSingleCode(c), l) == [c] + l
// {
//   match c {
//     case VarCode(s) => {
//       var ints := [0, |s|] + s;
//       calc {
//           DeserializeCodesRec(SerializeSingleCode(VarCode(s)), l);
//         ==
//           DeserializeCodesRec([0, |s|] + s, l);
//         ==
//           DeserializeCodesRec(ints, l);
//         ==
//           DeserializeCodesRec(ints[2..][(ints[1])..], [VarCode(ints[2..][..(ints[1])])] + l);
//         ==
//           DeserializeCodesRec([], [VarCode(ints[2..][..(ints[1])])] + l);
//         ==
//           DeserializeCodesRec([], [VarCode(s[..(ints[1])])] + l);
//         ==
//           DeserializeCodesRec([], [VarCode(s[..(|s|)])] + l);
//         == { assert s[..|s|] == s; }
//           DeserializeCodesRec([], [VarCode(s)] + l);
//         ==
//           [c] + l;
//       }
//     }
//     case ValCode(i) => calc {
//           DeserializeCodesRec(SerializeSingleCode(ValCode(i)), l);
//         ==
//           DeserializeCodesRec([1, i], l);
//         ==
//           DeserializeCodesRec([1, i], l);
//         ==
//           DeserializeCodesRec([], [ValCode(i)] + l);
//         ==
//           [c] + l;
//     }
//     case UnOpCode(uop) => calc {
//           DeserializeCodesRec(SerializeSingleCode(UnOpCode(uop)), l);
//         ==
//           DeserializeCodesRec([], [UnOpCode(Neg)] + l);
//         == {assert uop == Neg;}
//           [c] + l;
//     }
//     // Can i use the match inside a calc ?
//     case BinOpCode(bop) => match bop {
//       case Plus => calc {
//           DeserializeCodesRec(SerializeSingleCode(BinOpCode(bop)), l);
//         == { assert Plus == bop; } // why is this needed?
//           DeserializeCodesRec([], [BinOpCode(Plus)] + l);
//         ==
//           [c] + l;
//       }
//       case Minus => calc {
//           DeserializeCodesRec(SerializeSingleCode(BinOpCode(bop)), l);
//         ==
//           DeserializeCodesRec([], [BinOpCode(Minus)] + l);
//         ==
//           [c] + l;
//       }
//     }
//   }
// }

// lemma DeserializeSingleCodeProperty(c : code)
//   ensures DeserializeCodes(SerializeSingleCode(c)) == [c]
// {
//   match c {
//     case VarCode(s) => {
//       var ints := [0, |s|] + s;
//       calc {
//           DeserializeCodes(SerializeSingleCode(VarCode(s)));
//         ==
//           DeserializeCodesRec([0, |s|] + s, []);
//         == 
//           DeserializeCodesRec(ints, []);
//         ==
//           DeserializeCodesRec(ints[2..][(ints[1])..], [VarCode(ints[2..][..(ints[1])])] + []);
//         ==
//           DeserializeCodesRec([], [VarCode(ints[2..][..(ints[1])])] + []);
//         ==
//           DeserializeCodesRec([], [VarCode(s[..(ints[1])])] + []);
//         ==
//           DeserializeCodesRec([], [VarCode(s[..(|s|)])] + []);
//         == { assert s[..|s|] == s; }
//           DeserializeCodesRec([], [VarCode(s)] + []);
//         ==
//           [c];
//       }
//     }
//     case ValCode(i) => calc {
//           DeserializeCodes(SerializeSingleCode(ValCode(i)));
//         ==
//           DeserializeCodes([1, i]);
//         ==
//           DeserializeCodes([1, i]);
//         ==
//           DeserializeCodesRec([], [ValCode(i)] + []);
//         ==
//           [c];
//     }
//     case UnOpCode(uop) => calc {
//           DeserializeCodes(SerializeSingleCode(UnOpCode(uop)));
//         ==
//           DeserializeCodesRec([], [UnOpCode(Neg)] + []);
//         == {assert uop == Neg;}
//           [c];
//     }
//     // Can i use the match inside a calc ?
//     case BinOpCode(bop) => match bop {
//       case Plus => calc {
//           DeserializeCodes(SerializeSingleCode(BinOpCode(bop)));
//         == { assert Plus == bop; } // why is this needed?
//           DeserializeCodesRec([], [BinOpCode(Plus)] + []);
//         ==
//           [c];
//       }
//       case Minus => calc {
//           DeserializeCodes(SerializeSingleCode(BinOpCode(bop)));
//         ==
//           DeserializeCodesRec([], [BinOpCode(Minus)] + []);
//         ==
//           [c];
//       }
//     }
//   }
// }

/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
  SerializeCodes(Serialize(e))
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
  Deserialize(DeserializeCodes(nats))
}

/*
  Ex1.6
*/
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