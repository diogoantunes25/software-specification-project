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
	// There's a single ring, not multiple small rings
	all n: Member | Member = n.*(nxt)

	// Members can't appear in member queues
	no (Node.(Member.qnxt) & Member)

	// The member queues are not multiple small queues
	// In particular, if there's a queue, the member can reach
	// everyone in the queue using the next
	// Node.(n.qnxt) => all people in the queue
	// n.^(n.qnxt) => all people reachable from n using the nxt of the queue
	all n: Member | Node.(n.qnxt) = n.^(n.qnxt)

	// Only non-leader members appear in leader queue
	no (Member.(Leader.lnxt) & Leader)

	// Leader queue are the members to which lnxt points
	LQueue = Member.(Leader.lnxt)

	// The leader queues are not multiple small queues
	// In particular, if there's a queue, the leader can reach
	// everyone in the queue using the next
	// Member.(Leader.lnxt) => all members in the queue
	// Leader.^(Leader.qnxt) => all members reachable from leader
	LQueue = Leader.^(Leader.lnxt)

	// Leader queue should be injective
	// FIXME: why doesn't this work?
	// Leader.lnxt in Member one -> lone Member

	// Leader queue should be injective
	all m: LQueue | one (Leader.lnxt).m
	
	// Member queues should be injective and node can only be in a single member queue
	all n: Node | lone (Member.qnxt).n
}

// Message consistency-constraints
fact {}

run example {
	no Msg
}
