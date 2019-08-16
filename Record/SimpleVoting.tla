---------------------------- MODULE SimpleVoting ----------------------------
EXTENDS Naturals
-----------------------------------------------------------------------------
CONSTANT Participant

VARIABLE maxBal

TypeOK == maxBal \in [Participant -> Nat]
-----------------------------------------------------------------------------
Init == maxBal = [p \in Participant |-> 0]

IncreaseMaxBal(p, b) ==
  /\ maxBal[p] < b
  /\ maxBal' = [maxBal EXCEPT ![p] = b]
-----------------------------------------------------------------------------
Next == \E p \in Participant, b \in Nat : IncreaseMaxBal(p, b)

Spec == Init /\ [][Next]_maxBal
=============================================================================
\* Modification History
\* Last modified Thu Aug 15 12:07:49 CST 2019 by hengxin
\* Created Thu Aug 15 11:12:58 CST 2019 by hengxin