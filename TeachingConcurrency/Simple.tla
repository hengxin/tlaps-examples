------------------------------- MODULE Simple -------------------------------
(*
See the paper "Teaching Concurrency" by Leslie Lamport for the problem
(https://www.microsoft.com/en-us/research/uploads/prod/2016/12/Teaching-Concurrency.pdf).

See also the StackOverflow post "What is the inductive invariant of the simple concurrent program?" 
(https://stackoverflow.com/q/24989756/1833118).

See the answer (https://stackoverflow.com/a/46108331/1833118) to the post above 
for the TLA+ specification and TLAPS proof.
*)
EXTENDS Integers, TLAPS
------------------------------------------------------------------------------
CONSTANTS N \* the number of processes
------------------------------------------------------------------------------
(*
--algorithm Simple

variables
    x = [i \in 0 .. N-1 |-> 0];
    y = [i \in 0 .. N-1 |-> 0];

process Proc \in 0 .. N-1 
begin
    s1: x[self] := 1;
    s2: y[self] := x[(self - 1) % N]
end process

end algorithm
*)
------------------------------------------------------------------------------
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0 .. N-1)

Init == (* Global variables *)
        /\ x = [i \in 0 .. N-1 |-> 0]
        /\ y = [i \in 0 .. N-1 |-> 0]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ x' = [x EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ y' = y

s2(self) == /\ pc[self] = "s2"
            /\ y' = [y EXCEPT ![self] = x[(self - 1) % N]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ x' = x

Proc(self) == s1(self) \/ s2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0 .. N-1: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
------------------------------------------------------------------------------
AtLeastOneYWhenDone == (\A i \in 0 .. N-1 : pc[i] = "Done") => \E i \in 0 .. N-1 : y[i] = 1

TypeOK == 
    /\ x \in [0 .. N-1 -> {0, 1}]
    /\ y \in [0 .. N-1 -> {0, 1}]
    /\ pc \in [ProcSet -> {"s1", "s2", "Done"}]

Inv == 
    /\ TypeOK
    /\ \A i \in 0 .. N-1 : (pc[i] \in {"s2", "Done"} => x[i] = 1)
    /\ AtLeastOneYWhenDone
------------------------------------------------------------------------------
ASSUME NIsInNat == N \in Nat \ {0}       

\* TLAPS doesn't know this property of modulus operator
AXIOM ModInRange == \A i \in 0 .. N-1: (i-1) % N \in 0 .. N-1

THEOREM Spec => []AtLeastOneYWhenDone
<1> USE DEF ProcSet, Inv
<1>1. Init => Inv
    BY NIsInNat DEF Init, Inv, TypeOK, AtLeastOneYWhenDone
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE Next
    <3>1. CASE \E self \in 0..N-1: Proc(self)
      <4> SUFFICES ASSUME NEW self \in 0..N-1, Proc(self)
                   PROVE  Inv'
        BY <3>1 
      <4>1. CASE s1(self)
        BY <4>1, NIsInNat DEF s1, TypeOK, AtLeastOneYWhenDone
      <4>2. CASE s2(self)
        BY <4>2, NIsInNat, ModInRange DEF s2, TypeOK, AtLeastOneYWhenDone
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF Proc
    <3>2. CASE (\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars
        BY <3>2 DEF TypeOK, vars, AtLeastOneYWhenDone
    <3>3. QED
      BY <2>1, <3>1, <3>2 DEF Next, Terminating
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF TypeOK, vars, AtLeastOneYWhenDone
  <2>3. QED
    BY <2>1, <2>2
<1>3. Inv => AtLeastOneYWhenDone
    OBVIOUS
<1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Wed Aug 07 17:32:20 CST 2019 by hengxin
\* Created Fri Aug 02 13:28:48 CST 2019 by hengxin