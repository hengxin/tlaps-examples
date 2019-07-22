-------------------------------- MODULE PaxosTuple --------------------------
EXTENDS Integers, Sets
-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
Ballot ==  Nat
None == CHOOSE v : v \notin Ballot
-----------------------------------------------------------------------------
Message ==
       {"1a"} \X Ballot
  \cup {"1b"} \X Acceptor \X Ballot \X (Ballot \cup {-1}) \X (Value \cup {None})
  \cup {"2a"} \X Ballot \X Value
  \cup {"2b"} \X Acceptor \X Ballot \X Value
-----------------------------------------------------------------------------
VARIABLE maxBal,
         maxVBal, \* <<maxVBal[a], maxVal[a]>>: the vote with the largest ballot number cast by a;
         maxVal,  \* it is <<-1, None>> if a has not cast any vote.
         msgs

Send(m) == msgs' = msgs \cup {m}

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message
-----------------------------------------------------------------------------
Init == /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVal = [a \in Acceptor |-> None]
        /\ msgs = {}

Phase1a(b) == /\ Send(<<"1a", b>>)
              /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) == /\ \E m \in msgs :
                  /\ m[1] = "1a"
                  /\ m[2] > maxBal[a]
                  /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
                  /\ Send(<<"1b", a, m[2], maxVBal[a], maxVal[a]>>)
              /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m[1] = "2a" /\ m[3] = b
  /\ \E Q \in Quorum :
        LET Q1b == {m \in msgs : /\ m[1] = "1b"
                                 /\ m[2] \in Q
                                 /\ m[3] = b}
            Q1bv == {m \in Q1b : m[4] \geq 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m[2] = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m[5] = v
                    /\ \A mm \in Q1bv : m[4] \geq mm[4]
  /\ Send(<<"2a", b, v>>)
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) == \E m \in msgs : /\ m[1] = "2a"
                              /\ m[2] \geq maxBal[a]
                              /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
                              /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
                              /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
                              /\ Send(<<"2b", a, m[2], m[3]>>)
----------------------------------------------------------------------------
Next == \/ \E b \in Ballot : \/ Phase1a(b)
                             \/ \E v \in Value : Phase2a(b, v)
        \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------
votes == [a \in Acceptor |->
           {<<m[3], m[4]>> : m \in {mm \in msgs: /\ mm[1] = "2b"
                                                 /\ mm[2] = a }}]
V == INSTANCE Voting

THEOREM Spec => V!Spec
============================================================================