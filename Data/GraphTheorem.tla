---------------------------- MODULE GraphTheorem ----------------------------
EXTENDS Sets, TLAPS

\* CONSTANT Nodes
\* ASSUME NodesFinite == IsFiniteSet(Nodes)

Edges(Nodes) == { {m[1], m[2]} : m \in Nodes \X Nodes }
  (*************************************************************************)
  (* The definition we want is                                             *)
  (*                                                                       *)
  (*    Edges == {{m, n} : m, n \in Nodes}                                 *)
  (*                                                                       *)
  (* However, this construct isn't supported by TLAPS yet.                 *)
  (*************************************************************************)

THEOREM EdgesAxiom == \A Nodes :
                       /\ \A m, n \in Nodes : {m, n} \in Edges(Nodes)
                       /\ \A e \in Edges(Nodes) :
                            \E m, n \in Nodes : e = {m, n}
BY IsaM("force") DEF Edges

-------------------------------------------------------
THEOREM EdgesFinite == \A Nodes :
                          IsFiniteSet(Nodes) => IsFiniteSet(Edges(Nodes))
PROOF OMITTED

NonLoopEdges(Nodes) == {e \in Edges(Nodes) : Cardinality(e) = 2}
SimpleGraphs(Nodes) == SUBSET NonLoopEdges(Nodes)
Degree(n, G) == Cardinality ({e \in G : n \in e})

THEOREM AtLeastTwo == ASSUME NEW S,
                             IsFiniteSet(S),
                             Cardinality(S) > 1
                      PROVE  \E x, y \in S : x # y
BY CardinalityAxiom, CardinalityInNat, SMT DEF IsBijection

------------------------------------------------------------------
(***************************************************************************)
(* Here's an informal proof of the following theorem                       *)
(*                                                                         *)
(* THEOREM For any finite graph G with no self loops and with more than 1  *)
(* node, there exist two nodes with the same degree.                       *)
(*                                                                         *)
(* <1>1. It suffices to assume G has at most one node with degree 0.       *)
(*   PROOF The theorem is obviously true if G has two nodes with degree 0. *)
(* <1>2. Let H be the subgraph of G obtained by eliminating all            *)
(*       nodes of degree 0.                                                *)
(* <1>3. H as at least 1 node.                                             *)
(*   PROOF By <1>1 and the assumption that G has                           *)
(*       more than one node.                                               *)
(* <1>4. The degree of every node in H is greater than 1 and less than     *)
(*       Cardinality(H).                                                   *)
(*   <2>1. For any node n of H, Degree(n, H) > 0                           *)
(*     PROOF by definition of H.                                           *)
(*         Degree(n, H) < Cardinality                                      *)
(*                                                                         *)
(* <1>5. QED                                                               *)
(*   BY <1>4 and the pigeonhole principle                                  *)
(*                                                                         *)
(* The formal proof doesn't follow exactly this structure.                 *)
(***************************************************************************)
THEOREM
  ASSUME NEW Nodes, IsFiniteSet(Nodes), Cardinality(Nodes) > 1,
         NEW G \in SimpleGraphs(Nodes)
  PROVE  \E m, n \in Nodes : /\ m # n
                             /\ Degree(m, G) = Degree(n, G)
<1>3. SUFFICES ASSUME \A m, n \in Nodes :
                         (m # n) => Degree(m, G) # Degree(n, G)
               PROVE  FALSE
  BY <1>3
<1>4. CASE \E m, n \in Nodes : /\ Degree(m, G) = 0
                               /\ Degree(n, G) = 0
                               /\ (m # n)
  BY <1>3, <1>4
<1>5. CASE \A m, n \in Nodes : /\ Degree(m, G) = 0
                               /\ Degree(n, G) = 0
                               => (m = n)
  <2>1. /\ G \subseteq NonLoopEdges(Nodes)
        /\ \A e \in G : /\ e \in Edges(Nodes)
                        /\ Cardinality(e) = 2
    BY DEF SimpleGraphs, NonLoopEdges
  <2>2. DEFINE Isolated  == {n \in Nodes : Degree(n, G) = 0}
               Connected == Nodes \ Isolated
  <2>2a. /\ IsFiniteSet(Connected)
         /\ Cardinality(Connected) \in Nat
    BY FiniteSubset, CardinalityInNat
  <2>3. /\ IsFiniteSet(Isolated)
        /\ Cardinality(Isolated) \in Nat
        /\ Cardinality(Isolated) \leq 1
    <3>1. IsFiniteSet(Isolated)
      BY FiniteSubset
    <3>2. Cardinality(Isolated) \in Nat
      BY <3>1, CardinalityInNat
    <3>3. CASE Cardinality(Isolated) > 1
      <4>1. PICK x \in Isolated, y \in Isolated : x # y
        BY AtLeastTwo, <3>1, <3>3, Blast
      <4>2. /\ x \in Nodes /\ Degree(x, G) = 0
            /\ y \in Nodes /\ Degree(y, G) = 0
        OBVIOUS
      <4>3. QED
        BY <1>5, <4>1, <4>2
    <3>4. QED
      BY <3>1, <3>2, <3>3, SMT
  <2>4. Cardinality(Connected) \geq 1
   <3>2. /\ Connected \cap Isolated = {}
         /\ Connected \cup Isolated = Nodes
     OBVIOUS
   <3>3. Cardinality(Nodes) = Cardinality(Connected) + Cardinality(Isolated)
                                - Cardinality(Connected \cap Isolated)
    <4>1. Cardinality(Connected \cup Isolated)
              = Cardinality(Connected) + Cardinality(Isolated)
                                - Cardinality(Connected \cap Isolated)
     BY <2>3, <2>2a, CardinalityUnion
    <4>2. QED
      BY <4>1, <3>2
   <3>4. Cardinality(Connected \cap Isolated) = 0
     BY <3>2, CardinalityZero
   <3>7. QED
     BY <2>3, <2>2a, <3>4, <3>3, SMT
  <2>5. ASSUME NEW e \in G, NEW n \in e
        PROVE  /\ n \in Nodes
               /\ n \notin Isolated
    <3>2. n \in Nodes
      BY <2>1, EdgesAxiom, SMT
    <3>3. Degree(n, G) # 0
      <4>2. IsFiniteSet({ee \in G : n \in ee})
        <5>1. IsFiniteSet(Edges(Nodes))
          BY EdgesFinite
        <5>2. IsFiniteSet(NonLoopEdges(Nodes))
            BY  <5>1, FiniteSubset  DEF NonLoopEdges
        <5>3. IsFiniteSet(G)
          BY <5>2, FiniteSubset DEF SimpleGraphs
        <5>4. QED
          BY <5>3, FiniteSubset
      <4>3. Cardinality({ee \in G : n \in ee}) # 0
        BY <4>2, CardinalityZero
      <4>4. QED
         BY <4>3 DEF Degree
    <3>4. QED
      BY <3>2, <3>3
  <2>6. \A n \in Connected : /\ Degree(n, G) \in Nat
                             /\ Degree(n, G) < Cardinality(Connected)
   <3>1. \A n \in Nodes : Degree(n, G) \in Nat
     <4>1. Edges(Nodes) \subseteq SUBSET Nodes
       BY DEF Edges
     <4>2. IsFiniteSet(Edges(Nodes))
       BY <4>1, SubsetsFinite, FiniteSubset
     <4>4. IsFiniteSet(NonLoopEdges(Nodes))
       BY <4>2, FiniteSubset DEF NonLoopEdges
     <4>5. IsFiniteSet(G)
       BY <2>1, <4>4, FiniteSubset
     <4>7. \A n \in Nodes : IsFiniteSet({e \in G : n \in e})
       BY <4>5, FiniteSubset
     <4>8. QED
       BY <4>7, CardinalityAxiom DEF Degree
   <3>2. ASSUME NEW e \in G,
                NEW n \in e
         PROVE  \E m \in Connected : n # m /\ e = {m, n}
     <4>2. /\ e \in Edges(Nodes)
           /\ Cardinality(e) = 2
        BY DEF SimpleGraphs, NonLoopEdges
     <4>3. PICK m \in Nodes, p \in Nodes : e = {m, p}
       BY <4>2, EdgesAxiom, IsaM("auto")
     <4>4. m # p
       BY <4>2, <4>3, CardinalityOne
     <4>4a. m \in Connected /\ p \in Connected
       BY <2>5, <4>3
     <4>5. n \in {m, p}
       BY <4>3
     <4>8. QED
       BY <4>4, <4>4a, <4>3, <4>5
   <3>3. SUFFICES ASSUME NEW n \in Connected
                  PROVE  Cardinality({e \in G : n \in e}) <
                            Cardinality(Connected)
     BY <3>1, <3>3 DEF Degree
   <3> DEFINE  nEdges == {e \in G : n \in e}
               PossibleNEdges == {{m, n} : m \in Connected \ {n}}
   <3>4. /\ nEdges \subseteq PossibleNEdges
         /\ IsFiniteSet(PossibleNEdges)
         /\ Cardinality(PossibleNEdges) \in Nat
         /\ Cardinality(nEdges) \in Nat
         /\ Cardinality(nEdges) \leq Cardinality(PossibleNEdges)
     <4>1. nEdges \subseteq PossibleNEdges
       BY <3>2
     <4>2. PossibleNEdges \subseteq SUBSET Nodes
       OBVIOUS
     <4>4. IsFiniteSet(PossibleNEdges) /\ Cardinality(PossibleNEdges) \in Nat
       BY <4>2, SubsetsFinite, FiniteSubset, CardinalityInNat
     <4>5. IsFiniteSet(nEdges)
        BY <4>1, <4>4, FiniteSubset
     <4>6. Cardinality(nEdges) \in Nat
       BY <4>5, CardinalityInNat
     <4>7. Cardinality(nEdges) \leq Cardinality(PossibleNEdges)
       BY <4>1, <4>4, FiniteSubset
     <4>8. QED
       BY <4>1, <4>4, <4>6, <4>7
   <3> DEFINE NC == Cardinality(Connected \ {n})
   <3>5. /\ IsFiniteSet(Connected \ {n})
         /\ NC \in Nat
         /\ NC < Cardinality(Connected)
     BY FiniteSubset, CardinalityInNat, CardinalitySetMinus, Z3
   <3>6. PICK f : IsBijection(f, 1..NC, Connected \ {n})
     BY <3>5, CardinalityAxiom
   <3>7. DEFINE g == [i \in 1..NC |-> {n, f[i]}]
   <3>8. IsBijection(g, 1..NC, PossibleNEdges)
     BY <3>6, Z3 DEF IsBijection
   <3>9. NC = Cardinality(PossibleNEdges)
     BY <3>4, <3>5, CardinalityAxiom, <3>8
   <3> HIDE DEF Connected, nEdges, PossibleNEdges, NC
   <3>10. Cardinality (nEdges) < Cardinality (Connected)
     BY ONLY <3>4, <3>5, <3>9, <2>2a, SMT
   <3> QED BY <3>10 DEF nEdges
        
         (******************************************************************)
         (* WITH i <- Cardinality(nEdges),                                 *)
         (*      j <- NC = Cardinality(PossibleNEdges)                     *)
         (*      k <- Cardinality(Connected)                               *)
         (******************************************************************)
  <2>7. DEFINE f == [n \in Connected |-> Degree(n, G)]
  <2>8. f \in [Connected -> 1 .. (Cardinality(Connected)-1)]
    BY <2>6, <2>2a, Z3
  <2>9. \E m, n \in Connected: m # n /\ f[m] = f[n]
    <3> HIDE DEF Connected, f
    <3> DEFINE CC1 == Cardinality(Connected)-1
    <3>1. /\ IsFiniteSet(1 .. CC1)
          /\ Cardinality(1 .. CC1) < Cardinality(Connected)
      <4>1 CASE Cardinality(Connected) = 1
        BY IntervalCardinality, <4>1
      <4>2 CASE Cardinality(Connected) > 1
        <5> CC1 \in Nat
          BY <2>2a, <4>2, SMT
        <5> IsFiniteSet(1..CC1)
          BY IntervalCardinality
        <5> Cardinality(1..CC1) = CC1 - 1 + 1
          BY IntervalCardinality
        <5> Cardinality(1..CC1) < Cardinality (Connected)
          BY <2>2a
        <5> QED
          OBVIOUS
      <4> QED
        BY <2>4, <2>2a, <4>1, <4>2
    <3> QED
      BY <2>2a, <2>4, <2>8, <3>1, PigeonHole
  <2>10. QED
    BY <1>3, <1>5, <2>9
<1>. QED
  BY <1>4, <1>5
=============================================================================
