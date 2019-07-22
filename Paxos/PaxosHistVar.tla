------------------------------- MODULE PaxosHistVar --------------------------
(*
Basic Paxos verified using only history variables.

See https://github.com/sachand/HistVar/blob/master/Basic%20Paxos/PaxosUs.tla
*)
EXTENDS Integers, TLAPS, NaturalsInduction

CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == Nat

VARIABLES sent

vars == <<sent>>

Send(m) == sent' = sent \cup {m}

None == CHOOSE v : v \notin Values

Init == sent = {}

(***************************************************************************)
(* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
(* with ballot b to a majority of acceptors.  It can do this only if it    *)
(* has not already sent a 1a message for ballot b.                         *)
(***************************************************************************)
Phase1a(b) == Send([type |-> "1a", bal |-> b])
              
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b and with the highest-numbered ballot   *)
(* (if any) for which it has voted for a value and the value it voted for  *)
(* in that ballot.  That promise is made in a 1b message.                  *)
(***************************************************************************)
last_voted(a) == LET 2bs == {m \in sent: m.type = "2b" /\ m.acc = a}
                 IN IF 2bs # {} THEN {m \in 2bs: \A m2 \in 2bs: m.bal >= m2.bal}
                    ELSE {[bal |-> -1, val |-> None]}

Phase1b(a) ==
  \E m \in sent, r \in last_voted(a):
     /\ m.type = "1a"
     /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal > m2.bal
     /\ Send([type |-> "1b", bal |-> m.bal,
              maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a])
        
(***************************************************************************)
(* Phase 2a: If the leader receives a response to its 1b message (for      *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b with a value v, where v is the     *)
(* value of the highest-numbered proposal among the responses, or is any   *)
(* value if the responses reported no proposals.  The leader can send only *)
(* one 2a message for any ballot.                                          *)
(***************************************************************************)
Phase2a(b) ==
  /\ ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b) 
  /\ \E v \in Values, Q \in Quorums, S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = b}:
       /\ \A a \in Q : \E m \in S : m.acc = a
       /\ \/ \A m \in S : m.maxVBal = -1
          \/ \E c \in 0..(b-1) : 
               /\ \A m \in S : m.maxVBal =< c
               /\ \E m \in S : /\ m.maxVBal = c
                               /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot numbered    *)
(* b, it votes for the message's value in ballot b unless it has already   *)
(* responded to a 1a request for a ballot number greater than or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
Phase2b(a) == 
  \E m \in sent :
    /\ m.type = "2a" 
    /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal >= m2.bal
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])

Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a) 

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  Wnat it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(v) means that v  *)
(* has been chosen.  From this definition, it is obvious how a process     *)
(* learns that a value has been chosen from messages of type "2b".         *)
(***************************************************************************)
VotedForIn(a, v, b) == \E m \in sent : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
-----------------------------------------------------------------------------
(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK == sent \in SUBSET Messages

(***************************************************************************)
(* WontVoteIn(a, b) is a predicate that implies that a has not voted and   *)
(* never will vote in ballot b.                                            *)
(***************************************************************************)                                       
WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ \E m \in sent: m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b

(***************************************************************************)
(* The predicate SafeAt(v, b) implies that no value other than perhaps v   *)
(* has been or ever will be chosen in any ballot numbered less than b.     *)
(***************************************************************************)                   
SafeAt(v, b) == 
  \A b2 \in 0..(b-1) :
    \E Q \in Quorums :
      \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)

MsgInv ==
  \A m \in sent : 
    /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                        /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
    /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                        /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
    /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                         /\ m2.bal  = m.bal
                                         /\ m2.val  = m.val

Inv == TypeOK /\ MsgInv

(***************************************************************************)
(* The following two lemmas are simple consequences of the definitions.    *)
(***************************************************************************)
LEMMA VotedInv == 
        MsgInv /\ TypeOK => 
            \A a \in Acceptors, v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => SafeAt(v, b)
BY DEF VotedForIn, MsgInv, Messages, TypeOK

LEMMA VotedOnce == 
        MsgInv =>  \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
                       VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
BY DEF MsgInv, VotedForIn
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b) is stable, meaning that once it becomes true, it *)
(* remains true throughout the rest of the excecution.                     *)
(***************************************************************************)
LEMMA SafeAtStable == Inv /\ Next => 
                          \A v \in Values, b \in Ballots:
                                  SafeAt(v, b) => SafeAt(v, b)'
<1> SUFFICES ASSUME Inv, Next,
                    NEW v \in Values, NEW b \in Ballots, SafeAt(v, b)
             PROVE  SafeAt(v, b)'
  OBVIOUS
<1> USE DEF Send, Inv, Ballots
<1> USE TRUE /\ TRUE
<1>1. ASSUME NEW bb \in Ballots, Phase1a(bb)
      PROVE  SafeAt(v, b)'
  BY <1>1, SMT DEF SafeAt, Phase1a, VotedForIn, WontVoteIn
<1>2. ASSUME NEW a \in Acceptors, Phase1b(a)
      PROVE  SafeAt(v, b)'
  BY <1>2, QuorumAssumption, SMTT(60) DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase1b
<1>3. ASSUME NEW bb \in Ballots, Phase2a(bb)
      PROVE  SafeAt(v, b)'
  BY <1>3, QuorumAssumption, SMT DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase2a
<1>4. ASSUME NEW a \in Acceptors, Phase2b(a)
      PROVE  SafeAt(v, b)'
  <2>1. PICK m \in sent : Phase2b(a)!(m)
    BY <1>4 DEF Phase2b
  <2>2 \A aa \in Acceptors, bb \in Ballots, vv \in Values :
            VotedForIn(aa, vv, bb) => VotedForIn(aa, vv, bb)'
    BY <2>1 DEF TypeOK, VotedForIn
  <2>4. ASSUME NEW a2 \in Acceptors, NEW b2 \in Ballots,
               WontVoteIn(a2, b2), NEW v2 \in Values
        PROVE  ~VotedForIn(a2, v2, b2)'
    <3>1. PICK m1 \in sent: m1.type \in {"1b", "2b"} /\ m1.acc = a2 /\ m1.bal > b2
      BY <2>4 DEF WontVoteIn
    <3>2. a2 = a => b2 # m.bal
      BY <2>1, <2>4, <3>1, a2 = a => m.bal >= m1.bal DEF TypeOK, Messages
    <3>3. a2 # a => ~VotedForIn(a2, v2, b2)'
      BY <2>1, <2>4 DEF WontVoteIn, VotedForIn
    <3>. QED
      BY <2>1, <2>2, <2>4, <3>2, <3>3 DEF Phase2b, VotedForIn, WontVoteIn, TypeOK, Messages, Send
  <2>5 \A aa \in Acceptors, bb \in Ballots : WontVoteIn(aa, bb) => WontVoteIn(aa, bb)'
    BY <2>4, <2>1 DEF WontVoteIn, Send
  <2> QED
    BY <2>2, <2>5, QuorumAssumption DEF SafeAt
                         
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots, last_voted
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, MsgInv, VotedForIn
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, Next
               PROVE  Inv'
    BY DEF vars, Inv, TypeOK, MsgInv, VotedForIn, SafeAt, WontVoteIn
  <2> USE DEF Inv
  <2>1. TypeOK'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE TypeOK'
      BY <3>1 DEF TypeOK, Phase1a, Send, Messages
    <3>2. ASSUME NEW b \in Ballots, Phase2a(b) PROVE TypeOK'
      <4>1. PICK v \in Values :
               Send([type |-> "2a", bal |-> b, val |-> v])
        BY <3>2 DEF Phase2a
      <4>. QED
        BY <4>1 DEF TypeOK, Send, Messages
    <3>3. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE TypeOK'
      <4>. PICK m \in sent, r \in last_voted(a): Phase1b(a)!(m, r)
        BY <3>3 DEF Phase1b
      <4>. QED
        BY DEF Send, TypeOK, Messages
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE TypeOK'
      <4>. PICK m \in sent : Phase2b(a)!(m)
        BY <3>4 DEF Phase2b
      <4>. QED 
        BY DEF Send, TypeOK, Messages
    <3>. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>3. MsgInv'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b)
          PROVE  MsgInv'
      <4>1. \A aa,vv,bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY <3>1 DEF Send, VotedForIn, Phase1a
      <4> QED
        BY <3>1, <4>1, QuorumAssumption, SafeAtStable DEF Phase1a, MsgInv, TypeOK, Messages, Send
    <3>2. ASSUME NEW a \in Acceptors, Phase1b(a)
          PROVE  MsgInv'
      <4>. PICK m \in sent, r \in last_voted(a): Phase1b(a)!(m, r)
        BY <3>2 DEF Phase1b
      <4>1. \A aa,vv,bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY DEF Send, VotedForIn
      <4>. DEFINE m2 == [type |-> "1b", bal |-> m.bal, maxVBal |-> r.bal, 
                         maxVal |-> r.val, acc |-> a]
      <4>3. VotedForIn(m2.acc, m2.maxVal, m2.maxVBal) \/ m2.maxVBal = -1
        BY DEF TypeOK, Messages, VotedForIn
      <4>4. \A b \in (r.bal+1) .. (m2.bal-1) :
                ~ \E v \in Values : VotedForIn(m2.acc, v, b)
        BY DEF TypeOK, Messages, VotedForIn, Send
      <4>. QED
        BY <4>1, <4>3, <4>4, SafeAtStable DEF MsgInv, TypeOK, Messages, Send
    <3>3. ASSUME NEW b \in Ballots, Phase2a(b)
          PROVE  MsgInv'
      <4>1. ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b)
        BY <3>3 DEF Phase2a
      <4>2. PICK v \in Values, Q \in Quorums, S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = b} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) : 
                       /\ \A m \in S : m.maxVBal =< c
                       /\ \E m \in S : /\ m.maxVBal = c
                                       /\ m.maxVal = v
               /\ Send([type |-> "2a", bal |-> b, val |-> v])
        BY <3>3 DEF Phase2a
      <4>. DEFINE mm == [type |-> "2a", bal |-> b, val |-> v]
      <4>3. sent' = sent \cup {mm}
        BY <4>2 DEF Send
      <4>4. \A aa, vv, bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY <4>3 DEF VotedForIn
      <4>6. \A m,ma \in sent' : m.type = "2a" /\ ma.type = "2a" /\ ma.bal = m.bal
                                => ma = m
        BY <4>1, <4>3, Isa DEF MsgInv
      <4>10. SafeAt(v,b)
        <5>1. CASE \A m \in S : m.maxVBal = -1
          \* In that case, no acceptor in Q voted in any ballot less than b,
          \* by the last conjunct of MsgInv for type "1b" messages, and that's enough
          BY <5>1, <4>2 DEF TypeOK, MsgInv, SafeAt, WontVoteIn
        <5>2. ASSUME NEW c \in 0 .. (b-1),
                     \A m \in S : m.maxVBal =< c,
                     NEW ma \in S, ma.maxVBal = c, ma.maxVal = v
              PROVE  SafeAt(v,b)
          <6>. SUFFICES ASSUME NEW d \in 0 .. (b-1)
                        PROVE  \E QQ \in Quorums : \A q \in QQ : 
                                  VotedForIn(q,v,d) \/ WontVoteIn(q,d)
            BY DEF SafeAt
          <6>1. CASE d \in 0 .. (c-1)
            \* The "1b" message for v with maxVBal value c must have been safe
            \* according to MsgInv for "1b" messages and lemma VotedInv, 
            \* and that proves the assertion
            BY <5>2, <6>1, VotedInv DEF SafeAt, MsgInv, TypeOK, Messages
          <6>2. CASE d = c
            <7>1. VotedForIn(ma.acc, v, c)
              BY <5>2 DEF MsgInv
            <7>2. \A q \in Q, w \in Values : VotedForIn(q, w, c) => w = v
              BY <7>1, VotedOnce, QuorumAssumption DEF TypeOK, Messages
            <7>. QED
              BY <6>2, <4>2, <7>2 DEF WontVoteIn
          <6>3. CASE d \in (c+1) .. (b-1)
            \* By the last conjunct of MsgInv for type "1b" messages, no acceptor in Q
            \* voted at any of these ballots.
            BY <6>3, <4>2, <5>2 DEF MsgInv, TypeOK, Messages, WontVoteIn
          <6>. QED  BY <6>1, <6>2, <6>3
        <5>. QED  BY <4>2, <5>1, <5>2
      <4>11. (\A m2 \in sent: m2.type = "2a" => SafeAt(m2.val, m2.bal))'
        BY <4>10, <4>3, SafeAtStable DEF MsgInv, TypeOK, Messages
      <4>. QED
         BY <4>3, <4>4, <4>6, <4>11, \A m2 \in sent' \ sent: m2.type # "1b"
           DEF MsgInv, TypeOK, Messages
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a)
          PROVE  MsgInv'
      <4>. PICK m \in sent : Phase2b(a)!(m)
        BY <3>4 DEF Phase2b
      <4>1. \A aa, vv, bb : VotedForIn(aa,vv,bb) => VotedForIn(aa,vv,bb)'
        BY DEF VotedForIn, Send
      <4>2. \A mm \in sent : mm.type = "1b"
               => \A v \in Values, c \in (mm.maxVBal+1) .. (mm.bal-1) :
                     ~ VotedForIn(mm.acc, v, c) => ~ VotedForIn(mm.acc, v, c)'
        BY DEF Send, VotedForIn, MsgInv, TypeOK, Messages
      <4>. QED
        BY <4>1, <4>2, SafeAtStable, <2>1 DEF MsgInv, Send, TypeOK, Messages
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>4. QED
    BY <2>1, <2>3 DEF Inv
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballots
  
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv,  
                      NEW v1 \in Values,  NEW v2 \in Values, 
                      NEW b1 \in Ballots, NEW b2 \in Ballots,
                      ChosenIn(v1, b1), ChosenIn(v2, b2),
                      b1 =< b2
               PROVE  v1 = v2
    BY DEF Consistency, Chosen
  <2>1. CASE b1 = b2
    BY <2>1, VotedOnce, QuorumAssumption, SMTT(100) DEF ChosenIn, Inv
  <2>2. CASE b1 < b2
    <3>1. SafeAt(v2, b2)
      BY VotedInv, QuorumAssumption DEF ChosenIn, Inv
    <3>2. PICK Q2 \in Quorums : 
                  \A a \in Q2 : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
      BY <3>1, <2>2 DEF SafeAt
    <3>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
      BY DEF ChosenIn
    <3>4. QED
      BY <3>2, <3>3, QuorumAssumption, VotedOnce, Z3 DEF WontVoteIn, Inv
  <2>3. QED
    BY <2>1, <2>2

<1>2. QED
  BY Invariant, <1>1, PTL

=============================================================================
\* Modification History
\* Last modified Mon Jul 22 20:43:22 CST 2019 by hengxin
\* Last modified Sat Dec 09 09:56:40 EST 2017 by Saksham
\* Last modified Tue Nov 21 19:12:25 EST 2017 by saksh
\* Last modified Fri Nov 28 10:39:17 PST 2014 by lamport
\* Last modified Sun Nov 23 14:45:09 PST 2014 by lamport
\* Last modified Mon Nov 24 02:03:02 CET 2014 by merz
\* Last modified Sat Nov 22 12:04:19 CET 2014 by merz
\* Last modified Fri Nov 21 17:40:41 PST 2014 by lamport
\* Last modified Tue Mar 18 11:37:57 CET 2014 by doligez
\* Last modified Sat Nov 24 18:53:09 GMT-03:00 2012 by merz
\* Created Sat Nov 17 16:02:06 PST 2012 by lamport