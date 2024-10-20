sig Node {
	// Pending messages from node + sending messages from other nodes
	outbox: set Msg
}

sig Member in Node {
	// Next node in member ring
	nxt: one Node,

	// Member queue
	qnxt: Node -> lone Node
}

// Leader of ring
one sig Leader in Member {
	// Leader queue
	lnxt: Member -> lone Member
}

// Set of nodes in leader queue
sig LQueue in Member {}

// Set of nodes in member queue
fun MQueue[m: Member]: set Node {
	(m.qnxt).Node
}

abstract sig Msg {
	// Node where message originates
	sndr: Node,

	// Nodes that have received the message
	rcvrs: set Node
}

// Possible message states (there are no other states)
sig SentMsg, SendingMsg, PendingMsg extends Msg {}

// Member queue arcs
fun ArcInQueue: Node -> lone Node {
	Member.qnxt
}

// Leader queue arcs
fun ArcInLeaderQueue: Member -> lone Member {
	Leader.lnxt
}

// Topological constraints
fact {

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

	// ===============================================
	// Member Queue constraints

	// The member queue ends in the member
	all m: Member, n: MQueue[m] | m in n.^(m.qnxt)

	// No loops in member queues
	all m: Member, n: MQueue[m] | n not in n.^(m.qnxt)

	// Only non-member is member queues
	all m: Member | no (MQueue[m] & Member)

	// Only one starrts in member queue
	all m: Member | lone (MQueue[m] - Node.(m.qnxt))

	// Queues are disjoint
	all disj m1, m2: Member | no (MQueue[m1] & MQueue[m2])
}

// Message consistency-constraints
fact {

	// ===============================================
	// SentMsg constraints

	// Pending messages are only in outbox of sender
	all m: PendingMsg | outbox.m = m.sndr

	// Pending messages have no receivers
	no PendingMsg.rcvrs

	// ===============================================
	// SendingMsg constraints

	// Sending messages are in some outbox that not of the sender
	all m: SendingMsg | some (outbox.m - m.sndr)

	// Sending messages haven't been received by sender
	all m: SendingMsg | m.sndr not in m.rcvrs

	// FIXME: I feel like there should be more restrictions, but I'm not quite
	// sure which
	// I could require the sndr to be a member, but I don't see the point

	// ===============================================
	// SentMsg constraints

	// Sent messages are in not outbox
	no outbox.SentMsg

	// Sent messages have been received by leader
	all m: SentMsg | m.sndr in m.rcvrs

	// Sent messages have been received by someone that is not the leader
	// This disallows sending messages to oneself
	// FIXME: check if this is needed
	all m: SentMsg | some m.rcvrs - m.sndr

	// ===============================================
	// Other constraints

	// If a not pending message is in someone outbox, then it the node has received the message
	// In other words, the outbox of a node minus the pending is a subset of what he has received
	all n: Node | (n.outbox - PendingMsg) in rcvrs.n

	// FIXME: can a non-member have sending msg in outbox? (left while had sending messages in outbox)
}

run example {
	some SentMsg
	some SendingMsg
	some PendingMsg
}
