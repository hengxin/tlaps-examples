------------------------------ MODULE EuclidEx ------------------------------
EXTENDS GCD, TLAPS
-----------------------------------------------------------------------------
CONSTANTS M, N
ASSUME MNPosInt == 
    /\ M \in Nat \ {0}
    /\ N \in Nat \ {0}
(*******************************************************************
--algorithm Euclid {
  variables x = M, y = N ;
  { while (x # y) { if (x < y) { y := y - x }
                    else       { x := x - y }
                  };
  }
}
 *******************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = M
        /\ y = N
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>

Next == Lbl_1 \* Allow infinite stuttering to prevent deadlock on termination.
           \/ (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
PartialCorrectness ==
    (pc = "Done") => (x = y) /\ (x = GCD(M, N))

TypeOK == 
    /\ x \in Nat \ {0}
    /\ y \in Nat \ {0}

Inv == 
    /\ TypeOK
    /\ GCD(x, y) = GCD(M, N)
    /\ (pc = "Done") => (x = y)
-----------------------------------------------------------------------------
THEOREM Spec => []PartialCorrectness
<1>1. Init => Inv
  BY MNPosInt DEF Init, Inv, TypeOK 
<1>2. Inv /\ [Next]_vars => Inv'
  BY MNPosInt, GCD2, GCD3 DEF Inv, TypeOK, Next, Lbl_1, vars
<1>3. Inv => PartialCorrectness
  BY MNPosInt, GCD1 DEF Inv, TypeOK, PartialCorrectness
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Tue Jul 16 09:46:10 CST 2019 by hengxin
\* Created Mon Jul 15 16:59:12 CST 2019 by hengxin