sig Node {
	// Pending messages from node + sending messages from other nodes
	var outbox: set Msg
}

var sig Member in Node {
	// Next node in member ring
	var nxt: one Node,

	// Member queue
	var qnxt: Node -> lone Node
}

// Leader of ring
var one sig Leader in Member {
	// Leader queue
	var lnxt: Member -> lone Member
}

// Set of nodes in leader queue
// FIXME: turn to function
var sig LQueue in Member {}

// Tail of leader queue
// FIXME: lone instead of one probably
fun LTail: one Member {
	// Member.(Leader.lxt) -> nodes to whom someone points
	LQueue - Member.(Leader.lnxt)
}

// Head of leader queue
// FIXME: lone instead of one
fun LHead: one Member {
	(Leader.lnxt).Leader
}

// Set of nodes in member queue
fun MQueue[m: Member]: set Node {
	(m.qnxt).Node
}

// Tail in member queue
// FIXME: lone instead of one probably
fun MTail[m: Member]: one Node {
	// Node.(m.qnxt) -> nodes to whom someone points
	MQueue[m] - Node.(m.qnxt)
}

abstract sig Msg {
	// Node where message originates
	sndr: Node,

	// Nodes that have received the message
	var rcvrs: set Node
}

// Possible message states (there are no other states)
// FIXME: why can't I use extends
var sig SentMsg, SendingMsg, PendingMsg in Msg {}

// Member queue arcs
fun ArcInQueue: Node -> lone Node {
	Member.qnxt
}

// Leader queue arcs
fun ArcInLeaderQueue: Member -> lone Member {
	Leader.lnxt
}

abstract sig Step {}
one sig MemberExitStep, LeaderPromotionStep, LeaderApplicationStep, NonMemberExitStep, MemberPromotionStep, MemberApplicationStep, StutterStep, InitStep extends Step {}
one sig StepState {
	var s: Step
}

// TEMPORAL STUFF

// Initial state
pred init {
	// The set of members consists only of the leader
	Member = Leader
	
	// Ring is just the leader
	Member.nxt = Member // FIXME: needed ?

	// No one can want to be the leader
	no lnxt // FIXME: needed ?
	no LQueue

	// All messages are pending
	Msg = PendingMsg

	// No member is queueing to become a member
	no qnxt

	// FIXME: Message sets are disjoint
	no SendingMsg & SentMsg
	no SentMsg & PendingMsg
	no PendingMsg & SendingMsg

	StepState.s = InitStep
}

// Stuttering step
pred stutter {
	// TODO: factor into several stutter predicates
	Member' = Member
	Leader' = Leader
	LQueue' = LQueue	
	SentMsg' = SentMsg
	SendingMsg' = SendingMsg
	PendingMsg' = PendingMsg

	outbox' = outbox
	nxt' = nxt
	qnxt' = qnxt
	lnxt' = lnxt
	rcvrs' = rcvrs

	StepState.s' = StutterStep
}

// State transformer
pred trans {
	stutter
	or
	topologyChange
//	or
//	messageRoute
}

// Topology change state transformers
pred topologyChange {
	// FIXME: I can say Node - Member, but doesn't sound nice to have this here
	some n: Node, m: Member | memberApplication[n,m]
	or
	some m: Member | memberPromotion[m]
	or
	some n: Node, m: Member | nonMemberExit[n,m]
	or
	some m: Member | leaderApplication[m]
	or
	some m: Member | leaderPromotion[m]
	or
	some m: Member | memberExit[m]
}

// Non-member n applies to become member by joining m's queue
pred memberApplication[n: Node, m: Member] {
	// Pre conditions
	// node is not a member
	n not in Member
	// node is not already waiting to join in some queue
	n not in (Member.qnxt).Node

	// Post conditions
	// if there was no queue, now there's a queue
	no (m.qnxt) implies m.qnxt' = (n -> m) + m.qnxt
			    else m.qnxt' = (n -> MTail[m]) + m.qnxt

	// Frame conditions
	Member' = Member
	Leader' = Leader
	LQueue' = LQueue	
	SentMsg' = SentMsg
	SendingMsg' = SendingMsg
	PendingMsg' = PendingMsg

	outbox' = outbox
	nxt' = nxt
	all m2: Member - m | m2.qnxt' = m2.qnxt
	lnxt' = lnxt
	rcvrs' = rcvrs

	StepState.s' = MemberApplicationStep
}

// Member m promotes head of member queue to member
pred memberPromotion[m: Member] {
	// Pre conditions
	// there are nodes in member queue of m
	some m.qnxt

	// Post conditions
	// remove head from queue
	some (m.qnxt).(m.qnxt.m) implies
		m.qnxt' = m.qnxt - (m.qnxt.m -> m) - ((m.qnxt).(m.qnxt.m) -> m.qnxt.m) + ((m.qnxt).(m.qnxt.m) -> m)
		else no m.qnxt'
	// update member to point to head
	m.nxt' = m.qnxt.m
	// add head as member
	Member' = Member + (m.qnxt.m)
	// point new member to previous next
	m.qnxt.m.nxt' = m.nxt
	// member queue of new member is empty
	no (m.qnxt.m).qnxt'

	// Frame conditions
	Leader' = Leader
	LQueue' = LQueue	
	SentMsg' = SentMsg
	SendingMsg' = SendingMsg
	PendingMsg' = PendingMsg

	outbox' = outbox
	all m: Member - m | m.nxt' = m.nxt
	all m: Member - m | m.qnxt' = m.qnxt
	lnxt' = lnxt
	rcvrs' = rcvrs

	StepState.s' = MemberPromotionStep
}

// Non-member n exists m's member queue
pred nonMemberExit[n: Node, m: Member] {
	// Pre conditions
	n in MQueue[m]

	// Post conditions

	// if n is the last in the queue, then  just remove n from queue
	// if n is in the middle, change pointers appropriately
	n = MTail[m] implies m.qnxt' = m.qnxt - (n -> n.(m.qnxt))
				 else m.qnxt' = m.qnxt - (n -> n.(m.qnxt)) - ((m.qnxt).n -> n) + ((m.qnxt).n -> n.(m.qnxt))

	// Frame conditions
	Member' = Member
	Leader' = Leader
	LQueue' = LQueue	
	SentMsg' = SentMsg
	SendingMsg' = SendingMsg
	PendingMsg' = PendingMsg

	outbox' = outbox
	nxt' = nxt
	all m2: Member - m | m2.qnxt' = m2.qnxt
	lnxt' = lnxt
	rcvrs' = rcvrs

	StepState.s' = NonMemberExitStep
}

// Member m applies to be the leader
pred leaderApplication[m: Member] {
	// Pre conditions
	m not in (Leader + LQueue)

	// Post conditions
	LQueue' = LQueue + m
	no LQueue implies Leader.lnxt' = (m -> Leader)
			  else Leader.lnxt' = Leader.lnxt + (m -> LTail)

	// Frame conditions
	Member' = Member
	Leader' = Leader
	SentMsg' = SentMsg
	SendingMsg' = SendingMsg
	PendingMsg' = PendingMsg

	outbox' = outbox
	nxt' = nxt
	qnxt' = qnxt
	rcvrs' = rcvrs

	StepState.s' = LeaderApplicationStep
}

// m becomes the new leader
pred leaderPromotion[m: Member] {
	// Pre conditions
	// member is the head of the queue
	m = LHead
	// no ongoing broadcasts
	no SendingMsg
	// leader has sent all its messages
	no (Leader.outbox & PendingMsg)

	// Post conditions
	// head is the new leader
	LHead = Leader'
	// old leader has no longer a leader queue
	// no Leader.(lnxt') // if Leader is no longer leader, it doesn't have a leader queue
	// leader queue is moved to new leader
	LHead.(lnxt') = Leader.lnxt - (LHead -> Leader)
	// new leader is removed from leader queue
	LQueue' = LQueue - LHead

	// Frame conditions
	Member' = Member
	SentMsg' = SentMsg
	SendingMsg' = SendingMsg
	PendingMsg' = PendingMsg

	outbox' = outbox
	nxt' = nxt
	qnxt' = qnxt
	rcvrs' = rcvrs

	StepState.s' = LeaderPromotionStep
}

// m exits the ring
pred memberExit[m: Member] {
	// Pre conditions
	// m is not the leader
	m not in Leader
	// m is not in the leader queue
	m not in LQueue
	// m's member queue is empty
	no m.qnxt
	// all its messages are sent
	sndr.m in SentMsg

	// Post conditions
	// previous points to next
	nxt' = nxt - (m -> m.nxt) - (nxt.m -> m) + (nxt.m -> m.nxt)
	// remove node from members
	Member' = Member - m

	// Frame conditions
	Leader' = Leader
	LQueue' = LQueue	
	SentMsg' = SentMsg
	SendingMsg' = SendingMsg
	PendingMsg' = PendingMsg

	outbox' = outbox
	qnxt' = qnxt
	lnxt' = lnxt
	rcvrs' = rcvrs

	StepState.s' = MemberExitStep
}

// Message routing state transformers
pred messageRoute {

}

pred system {
	init
	always trans
}

fact {
	system
}

run example {
	no Msg
} for 3 but exactly 3 Node, 20 steps

