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
var sig LQueue in Member {}

// Tail of leader queue
fun LTail: lone Member {
	// Member.(Leader.lxt) -> nodes to whom someone points
	LQueue - Member.(Leader.lnxt)
}

// Head of leader queue
fun LHead: lone Member {
	(Leader.lnxt).Leader
}

// Set of nodes in member queue
fun MQueue[m: Member]: set Node {
	(m.qnxt).Node
}

// Tail in member queue
fun MTail[m: Member]: lone Node {
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
var sig SentMsg, SendingMsg, PendingMsg in Msg {}

// Member queue arcs
fun ArcInQueue: Node -> lone Node {
	Member.qnxt
}

// Leader queue arcs
fun ArcInLeaderQueue: Member -> lone Member {
	Leader.lnxt
}

// Auxiliary definitions to understand what happened
// at each step
abstract sig Step {}
one sig BroadcastTermStep, RedirectStep, BrodcastInitStep, MemberExitStep, LeaderPromotionStep, LeaderApplicationStep, NonMemberExitStep, MemberPromotionStep, MemberApplicationStep, StutterStep, InitStep extends Step {}
one sig StepState {
	var s: Step
}


// Initial state
pred init {
	// The set of members consists only of the leader
	Member = Leader
	
	// Ring is just the leader
	Member.nxt = Member

	// No one can want to be the leader
	no lnxt
	no LQueue

	// All messages are pending
	Msg = PendingMsg

	// Pending messages are in the correct member
	all n: Node | sndr.n = n.outbox

	// No one received messages
	no rcvrs

	// No member is queueing to become a member
	no qnxt

	// Types of messages are disjoint
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
	or
	messageRoute
}

// Topology change state transformers
pred topologyChange {
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

pred memberApplicationEnabled[n: Node, m: Member] {
	// node is not a member
	n not in Member
	// node is not already waiting to join in some queue
	n not in (Member.qnxt).Node
}

// Non-member n applies to become member by joining m's queue
pred memberApplication[n: Node, m: Member] {
	// Pre conditions
	memberApplicationEnabled[n,m]

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

pred memberPromotionEnabled[m: Member] {
	// there are nodes in member queue of m
	some m.qnxt
}

// Member m promotes head of member queue to member
pred memberPromotion[m: Member] {
	// Pre conditions
	memberPromotionEnabled[m]

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

pred nonMemberExitEnabled[n: Node, m: Member] {
	// node is a member queue
	n in MQueue[m]
}

// Non-member n exists m's member queue
pred nonMemberExit[n: Node, m: Member] {
	// Pre conditions
	nonMemberExitEnabled[n,m]

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

pred leaderApplicationEnabled[m: Member] {
	m not in (Leader + LQueue)
}

// Member m applies to be the leader
pred leaderApplication[m: Member] {
	// Pre conditions
	leaderApplicationEnabled[m]


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

pred leaderPromotionEnabled[m: Member] {
	// member is the head of the queue
	m = LHead
	// no ongoing broadcasts
	no SendingMsg
	// leader has sent all its messages
	no (Leader.outbox & PendingMsg)
}

// m becomes the new leader
pred leaderPromotion[m: Member] {
	// Pre conditions
	leaderPromotionEnabled[m]

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

pred memberExitEnabled[m: Member] {
	// m is not the leader
	m not in Leader
	// m is not in the leader queue
	m not in LQueue
	// m's member queue is empty
	no m.qnxt
	// all its messages are sent
	sndr.m in SentMsg
	// it has no redirect responsibilities
	no m.outbox
}

// m exits the ring
pred memberExit[m: Member] {
	// Pre conditions
	memberExitEnabled[m]

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
	some msg: Msg | broadcastInit[msg]
	or
	some msg: Msg, m: Member | redirect[m,msg]
	or
	some msg: Msg | broadcastTerm[msg]
}

pred broadcastInitEnabled[msg: Msg] {
	// message is pending
	msg in PendingMsg
	// message is from leader
	msg.sndr = Leader
	// the ring is not just the leader
	some Member - Leader
}

// Leader sends message to next node
pred broadcastInit[msg: Msg] {
	// Pre conditions
	broadcastInitEnabled[msg]

	// Post conditions
	// message is not sending
	PendingMsg' = PendingMsg - msg
	SendingMsg' = SendingMsg + msg
	// message is removed from leader outbox
	Leader.outbox' = Leader.outbox - msg
	// message is placed in next outbox
	Leader.nxt.outbox' = Leader.nxt.outbox + msg

	// Frame conditions
	Member' = Member
	Leader' = Leader
	LQueue' = LQueue	
	SentMsg' = SentMsg

	all n: Node - Leader - Leader.nxt | n.outbox' = n.outbox
	nxt' = nxt
	qnxt' = qnxt
	lnxt' = lnxt
	rcvrs' = rcvrs

	StepState.s' = BrodcastInitStep
}

pred redirectEnabled[m: Member, msg: Msg] {
	// message should have been broadcasted
	msg in SendingMsg
	// message should be in members outbox
	msg in m.outbox
	// member can't be the sender
	m != msg.sndr
}

// member m redirects msg to next node
pred redirect[m: Member, msg: Msg] {
	// Pre conditions
	redirectEnabled[m,msg]

	// Post conditions
	// only member gets new message and it's msg
	rcvrs' = rcvrs + {msg -> m}
	// message is removed from members outbox
	m.outbox' = m.outbox - msg
	// message is added to next's outbox
	m.nxt.outbox' = m.nxt.outbox + msg

	// Frame conditions
	Member' = Member
	Leader' = Leader
	LQueue' = LQueue	
	SentMsg' = SentMsg
	SendingMsg' = SendingMsg
	PendingMsg' = PendingMsg

	all m2: Node - (m + m.nxt) | m2.outbox' = m2.outbox
	nxt' = nxt
	qnxt' = qnxt
	lnxt' = lnxt
	
	StepState.s' = RedirectStep
}

pred broadcastTermEnabled[msg: Msg] {
	// message broadcast should be ongoing
	msg in SendingMsg
	// message should be in leader's outbox
	msg in Leader.outbox
}

// leader receives back one of the previous messages
pred broadcastTerm[msg: Msg] {
	// Pre conditions
	broadcastTermEnabled[msg]

	// Post conditions
	// only leader gets new message and it's msg
	// rcvrs' = rcvrs + (msg -> Leader)
	// message is removed from members outbox
	outbox' = outbox - (Leader -> msg)
	// message has now been sent
	SendingMsg' = SendingMsg - msg
	SentMsg' = SentMsg + msg

	// Frame conditions
	Member' = Member
	Leader' = Leader
	LQueue' = LQueue	
	PendingMsg' = PendingMsg

	nxt' = nxt
	qnxt' = qnxt
	lnxt' = lnxt
	rcvrs' = rcvrs

	StepState.s' = BroadcastTermStep
}

pred system {
	init
	always trans
}

// Topological constraints
pred topologyValid {

	// ===============================================
	// Ring constraints

	// There's a single ring, not multiple small rings
	all n: Member | Member = n.*(nxt)

	// ===============================================
	// Leader Queue constraints

	// Leader queue are the members from which lnxt points
	LQueue = (Leader.lnxt).Member

	// The leader queue ends in the leader
	all m: LQueue | Leader in m.^(Leader.lnxt)

	// No loops in leader queue
	all m: LQueue | m not in m.^(Leader.lnxt)

	// Only one start in leader queue
	// Member.(Leader.lnxt) = members pointed to by someone
	lone (LQueue - Member.(Leader.lnxt))

	// A member is only pointed at by one person

	// ===============================================
	// Member Queue constraints

	// The member queue ends in the member
	all m: Member, n: MQueue[m] | m in n.^(m.qnxt)

	// No loops in member queues
	all m: Member, n: MQueue[m] | n not in n.^(m.qnxt)

	// Only non-member is member queues
	all m: Member | no (MQueue[m] & Member)

	// Only one starts in member queue
	all m: Member | lone (MQueue[m] - Node.(m.qnxt))

	// Queues are disjoint
	all disj m1, m2: Member | no (MQueue[m1] & MQueue[m2])
}

// Message consistency-constraints
pred messageValid {

	// ===============================================
	// PendingMSg constraints

	// Pending messages are only in outbox of sender
	all m: PendingMsg | outbox.m = m.sndr

	// Pending messages have no receivers
	no PendingMsg.rcvrs

	// ===============================================
	// SendingMsg constraints

	// Sending messages are in some outbox
	all m: SendingMsg | some outbox.m


	// NOTE: this was required by the contraints on messages on the textfile
	// provided in the course page. However, I only add a node to the receivers
	// list on redirect, not on send, so this doesn't hold (this decision resulted
	// from an initial interpretation of the project statement)
	// Alternatively, this could be added. For that, the broadcast would add the
	// receivers to the node and so would the redirect. However, the redirect
	// would only do it if the receipient was not the leader (to ensure that leader
	// is not in receivers of message). Here is the constraint if it was to be added
	// All sending message have some receivers
	// rcvrs.Node = all message with some receiver
	// no (SendingMsg - rcvrs.Node)

	// Sending messages haven't been received by sender
	all m: SendingMsg | m.sndr not in m.rcvrs

	// Only leader can have sending messages
	no SendingMsg.sndr - Leader

	// ===============================================
	// SentMsg constraints

	// Sent messages are in no outbox
	no outbox.SentMsg

	// Sent messages have been received by someone that is not the leader
	// This disallows sending messages to oneself
	all m: SentMsg | some m.rcvrs - m.sndr

	// ===============================================
	// Other constraints

	// Node can't receive their own messages
	all m: Msg | no (m.rcvrs & m.sndr)

	// A message can only be in one outbox
	all m: Msg | lone outbox.m

	// A node can only be non-member if its outbox has no sending messages
	// in other words, nodes can't leave the ring with sending messages
	no (Node - Member).outbox - PendingMsg
}

pred valid {
	always (topologyValid and messageValid)
}

assert validityInvariant {
	system implies valid
}

pred fairnessMemberApplication {
 	all m: Member, n: Node |
		((eventually always memberApplicationEnabled[n,m]) implies
			(always eventually memberApplication[n,m]))
}

pred fairnessMemberPromotion {
	all m: Member | 
		(eventually always memberPromotionEnabled[m] implies always eventually memberPromotion[m])
}

pred fairnessLeaderApplication {
	all m: Member |
		((eventually always leaderApplicationEnabled[m]) implies (always eventually leaderApplication[m]))
}

pred fairnessLeaderPromotion {
	all m: Member |
		(eventually always leaderPromotionEnabled[m] implies always eventually leaderPromotion[m])
}

pred fairnessBroadcastInit {
	all msg: Msg |
		(eventually always broadcastInitEnabled[msg] implies always eventually broadcastInit[msg])
}

pred fairnessRedirect {
	all msg: Msg, m: Member |
		(eventually always redirectEnabled[m,msg] implies always eventually redirect[m,msg])
}

pred fairnessBroadcastTerm {
	all msg: Msg |
		(eventually always broadcastTermEnabled[msg] implies always eventually broadcastTerm[msg])
}

// always operator added when the set the predicate is quantifying over is mutable
// when that happens the quantification must be done at all instants
pred fairness {
	// Eventually every node should be able to join a member queue
	always fairnessMemberApplication

	// Eventually every node should be able to become a member
	always fairnessMemberPromotion

	// Eventually every member should become a leader
	always fairnessLeaderApplication
	always fairnessLeaderPromotion

	// Eventually every leader should send it's messages
	fairnessBroadcastInit
	always fairnessRedirect
	fairnessBroadcastTerm
}

// no exit operations are performed
pred noExit {
	always no { n: Node, m: Member | nonMemberExit[n,m] }
	and
	always no { m: Member | memberExit[m] }
}

pred atLeastTwoNodes {
	some Node - Leader
}

// all broadcasts terminate
pred allBroadcastsTerminate {
	eventually Msg = SentMsg
}

assert allTerminate3a {
	(atLeastTwoNodes and fairness and noExit) implies allBroadcastsTerminate
}

assert allTerminate4 {
	(atLeastTwoNodes and fairness) implies allBroadcastsTerminate
}

fact {
	system
}

// check validityInvariant

// confirm non triviality of antecedent of validityInvariant
// run example {} for exactly 5 Node, 3 Msg

// check allTerminate3a

//run example {
//	atLeastTwoNodes and fairness and noExit
// }

// yields the counter example
check allTerminate4
