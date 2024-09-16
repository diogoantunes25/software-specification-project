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


/*
  Ex1.1
*/
function Deserialize(cs : seq<code>) : seq<aexpr> 
{
  
}


/*
  Ex1.2
*/
lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [ e ]
{
 
}


/*
  Ex1.3
*/
function SerializeCodes(cs : seq<code>) : seq<nat> 
{

}

function DeserializeCodes(ints : seq<nat>) : seq<code> {
  
}


/*
  Ex1.4
*/
lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
}

/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
 
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 
}

/*
  Ex1.6
*/
lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
    
}