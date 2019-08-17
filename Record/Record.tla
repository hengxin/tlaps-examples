------------------------------- MODULE Record -------------------------------
EXTENDS Naturals, TLAPS
---------------------------------------------------------------------------
CONSTANTS Participant  \* the set of partipants

VARIABLES state \* state[p][q]: the state of q \in Participant from the view of p \in Participant
    
State == [maxBal: Nat, maxVBal: Nat]

TypeOK == state \in [Participant -> [Participant -> State]]
---------------------------------------------------------------------------
InitState == [maxBal |-> 0, maxVBal |-> 0]

Init == state = [p \in Participant |-> [q \in Participant |-> InitState]] 

Prepare(p, b) == 
    /\ state[p][p].maxBal < b
    /\ state' = [state EXCEPT ![p][p].maxBal = b]
---------------------------------------------------------------------------
Next == \E p \in Participant, b \in Nat : Prepare(p, b)

Spec == Init /\ [][Next]_state
---------------------------------------------------------------------------
(*
Record refines SimpleVoting
*)
maxBal == [p \in Participant |-> state[p][p].maxBal]

SV == INSTANCE SimpleVoting

THEOREM Invariant == Spec => []TypeOK
  OMITTED

THEOREM Spec => SV!Spec
  <1>1. Init => SV!Init
    BY DEF Init, SV!Init, maxBal, InitState
  <1>2. [Next]_state => [SV!Next]_maxBal
    <2>1. UNCHANGED state => UNCHANGED maxBal
      BY DEF maxBal
    <2>2. Next => SV!Next
      <3> SUFFICES ASSUME NEW p \in Participant, NEW b \in Nat,
                          Prepare(p, b)
                   PROVE  SV!IncreaseMaxBal(p, b)
        BY DEF Next, SV!Next
      <3>1. maxBal[p] < b
        BY DEF Prepare, maxBal
      <3>2. maxBal' = [maxBal EXCEPT ![p] = b] \* failed here!
        BY DEF Prepare, maxBal
      <3>3. QED
        BY <3>1, <3>2 DEF SV!IncreaseMaxBal
    <2>3. QED
      BY <2>1, <2>2
  <1>3. QED
    BY <1>1, <1>2, PTL DEF SV!Spec, Spec
=============================================================================
\* Modification History
\* Last modified Sat Aug 17 14:43:49 CST 2019 by hengxin
\* Created Thu Aug 15 10:52:49 CST 2019 by hengxin