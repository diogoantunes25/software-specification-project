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
	sndr: Node,
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
fact {}

run example {
	no Msg
	no lnxt
}
