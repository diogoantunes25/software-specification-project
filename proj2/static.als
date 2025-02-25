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
fact {

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

run example1 {
	some lnxt

	// Force two member queues (one at the leader)
	some (Member - Leader).qnxt
	some Leader.qnxt
	
	some SentMsg
	some SendingMsg
	some PendingMsg
} for exactly 5 Node, 3 Msg
