-------------------------- MODULE SequencesTheorems -------------------------
(***************************************************************************)
(* The proofs in this module were essentially written before TLAPS's SMT   *)
(* backend prover was implemented. That backend usually allows for much    *)
(* shorter proofs.                                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLAPS

AXIOM SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}

AXIOM LenDef == \A S : \A seq \in Seq(S) :
                     /\ Len(seq) \in Nat 
                     /\ DOMAIN seq = 1..Len(seq)

THEOREM LenAxiom == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ seq \in [1..Len(seq) -> S]
BY SeqDef, LenDef, SMT

THEOREM LenDomain == \A S :
                       \A s \in Seq(S) :
                         \A n \in Nat : DOMAIN s = 1..n => n = Len(s)
BY LenDef, SMT

AXIOM HeadDef == \A s : Head(s) = s[1]
AXIOM TailDef == \A s : Tail(s) = [i \in 1..(Len(s)-1) |-> s[i+1]]

AXIOM SubSeqDef ==
        \A s, m, n : SubSeq(s, m, n) = [i \in 1..(1+n-m) |-> s[i+m-1]]

THEOREM InitialSubSeq ==
   ASSUME NEW S,
          NEW s \in Seq(S),
          NEW j \in 0..Len(s)
   PROVE  /\ SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
          /\ SubSeq(s, 1, j) \in Seq(S)
          /\ Len(SubSeq(s, 1, j)) = j
<1>1. SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
  BY SubSeqDef, SMT
<1>2. SubSeq(s, 1, j) \in Seq(S)
  <2>1. j \in Nat
    BY LenDef, SMT
  <2>2. \A i \in 1..j : s[i] \in S
    <3>1. 1..j \subseteq 1 .. Len(s)
      BY SMT
    <3>2. QED
      BY <3>1, SeqDef, LenAxiom
  <2>3. QED
    BY <1>1, <2>1, <2>2, SeqDef, IsaM("force")
<1>3. Len(SubSeq(s, 1, j)) = j
  BY <1>1, <1>2, LenDef, DOMAIN SubSeq(s,1,j) = 1..j, j \in Nat, LenDomain
<1>4. QED
  BY <1>1, <1>2, <1>3

------------------------------------------------------------------
THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
BY LenAxiom

------------------------------------------------------------------
THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)
BY LenAxiom

------------------------------------------------------------------
THEOREM HeadAndTailOfSeq ==
   ASSUME NEW S,
          NEW seq \in Seq(S), seq # << >>
   PROVE  /\ Head(seq) \in S
          /\ Tail(seq) \in Seq(S)
  (*************************************************************************)
  (* Note: the way Tail is defined, Tail(<< >>) \in Seq(S) is actually     *)
  (* valid (because Tail(<< >>) = << >>).                                  *)
  (*************************************************************************)
<1>2. /\ Len(seq) \in Nat
      /\ Len(seq) # 0
  BY LenAxiom, EmptySeq
<1>3. Head(seq) \in S
  BY <1>2, HeadDef, LenDef, SMT
<1>4. Tail(seq) \in Seq(S)
  BY <1>2, LenAxiom, TailDef, SeqDef, SMT
<1>5. QED
  BY <1>3, <1>4

------------------------------------------------------------------
Remove(i, seq) == [j \in 1..(Len(seq)-1) |->
                                   IF j < i THEN seq[j] ELSE seq[j+1]]
THEOREM RemoveSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE   Remove(i, seq) \in Seq(S)
<1>4. \A j \in 1..(Len(seq)-1) :
          (IF j < i THEN seq[j] ELSE seq[j+1]) \in S
  BY LenAxiom, SMT
<1>5. Remove(i, seq) \in [1..(Len(seq)-1) -> S]
  BY <1>4 DEF Remove
<1>6. CASE Len(seq) # 0
  <2>1. Len(seq)-1 \in Nat
    BY <1>6, LenDef, SMT
  <2>2. QED
    BY <1>5, <2>1, SeqDef
<1>7. CASE Len(seq) = 0
  <2>1. 1 .. Len(seq)-1 = 1 .. 0
    BY <1>7, SMT
  <2>2. QED
    BY <1>5, <2>1, SeqDef
<1>8. QED
  BY <1>6, <1>7

-----------------------------------------------------------------------------
(***************************************************************************)
(*                                    Append                               *)
(***************************************************************************)
THEOREM AppendDef ==
   ASSUME NEW S, NEW seq \in Seq(S), NEW elt
   PROVE  Append(seq, elt) =
                [i \in 1..(Len(seq)+1) |-> IF i \leq Len(seq) THEN seq[i]
                                                              ELSE elt]
BY SMT

THEOREM AppendProperties ==
          \A S :
            \A seq \in Seq(S), elt \in S :
                /\ Append(seq, elt) \in Seq(S)
                /\ Len(Append(seq, elt)) = Len(seq)+1
                /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
                /\ Append(seq, elt)[Len(seq)+1] = elt
BY SMT
-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)
THEOREM ConcatDef ==
           \A S: 
           \A s1, s2 \in Seq(S) : s1 \o s2 =
                         [i \in 1..(Len(s1)+Len(s2)) |->
                           IF i \leq Len(s1) THEN s1[i]
                                             ELSE s2[i-Len(s1)]]
BY SMT

THEOREM ConcatProperties ==
           \A S :
             \A s1, s2 \in Seq(S) :
                 /\ s1 \o s2 \in Seq(S)
                 /\ Len(s1 \o s2) = Len(s1) + Len(s2)
BY ConcatDef, SMT

THEOREM ConcatEmptySeq ==
          \A S : \A seq \in Seq(S) : /\ seq \o << >> = seq
                                     /\ << >> \o seq = seq
PROOF OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Head and Tail                                 *)
(***************************************************************************)
THEOREM TailProp == \A S :
                    \A seq \in Seq(S) :
                       seq # << >> =>
                         /\ Tail(seq) \in Seq(S)
                         /\ Len(Tail(seq)) = Len(seq) - 1
                         /\ \A i \in 1..Len(Tail(seq)) :
                                 /\ i+1 \in 1..Len(seq)
                                 /\ Tail(seq)[i] = seq[i+1]
PROOF OMITTED


=============================================================================
