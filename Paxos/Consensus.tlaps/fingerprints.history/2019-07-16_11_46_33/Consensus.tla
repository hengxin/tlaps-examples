----------------------------- MODULE Consensus -----------------------------
(***************************************************************************)
(* This is a trivial specification of consensus.  It asserts that the      *)
(* variable `chosen', which represents the set of values that someone      *)
(* might think has been chosen is initially empty and can be changed only  *)
(* by adding a single element to it.                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLAPS
-----------------------------------------------------------------------------
CONSTANTS Values \* the set of all values that can be chosen

VARIABLES chosen \* the set of all values that have been chosen

TypeOK ==
    /\ chosen \subseteq Values
    /\ IsFiniteSet(chosen)
-----------------------------------------------------------------------------
Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}
        
Spec == Init /\ [][Next]_chosen
-----------------------------------------------------------------------------
Inv == Cardinality(chosen) <= 1
    \* /\ TypeOK
    \* /\ Cardinality(chosen) <= 1

THEOREM Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv
  (*
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2> QED
    BY DEF Init, Inv
  *)
  
<1>2. Inv /\ [Next]_chosen => Inv'
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Tue Jul 16 11:46:28 CST 2019 by hengxin
\* Last modified Tue Jul 16 11:26:27 CST 2019 by hengxin
\* Last modified Wed Nov 21 11:35:33 PST 2012 by lamport
\* Created Mon Nov 19 15:19:09 PST 2012 by lamport
