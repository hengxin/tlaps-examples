# tlaps-examples 

> Examples for TLA+ Proof System

Adapted from the examples accompany with [the tlaps tool](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries/Linux.html).

- [Euclid](https://github.com/hengxin/tlaps-examples/tree/master/Euclid)
  - [Euclid-Hyperbook](https://github.com/hengxin/tlaps-examples/tree/master/Euclid/Euclid-Hyperbook)
    - Proofs about Euclid's Algorithm. 
    - Ref: Chapter 11 "Correctness of Euclid's Algorithm" of Hyperbook
  - [Euclid-TLAPS-Example](https://github.com/hengxin/tlaps-examples/tree/master/Euclid/Euclid-TLAPS-Example)
    - Proofs about Euclid's Algorithm. 
    - From tlaps/examples


***TODO:*** re-organized

Allocator.tla:
   allocator managing a set of resources

Bakery.tla
AtomicBakery.tla
AtomicBakeryWithoutSMT.tla
   different versions of Lamport's bakery algorithm,
   Bakery.tla being the most faithful representation
   with non-atomic operations on shared registers

BubbleSort.tla
   the classic BubbleSort algorithm as a PlusCal
   algorithm, and its correctness proof

Euclid.tla
   proofs about Euclid's algorithm for computing the
   GCD of two positive integers, cf. the TLAPS tutorial

Peterson.tla:
   Peterson's algorithm for mutual exclusion
   between two processes using shared memory

SimpleMutex.tla:
   the essence of many mutual exclusion protocols

SumAndMax.tla:
   a simple challenge problem from VSTTE 2010

------------------------------------------------------------
Sub-directories:

paxos/Paxos.tla
   TLA+ specification of the Paxos consensus algorithm
   and a proof of its correctness (safety)

two-phase/*.tla
   two-phase handshake

cantor/Cantor*.tla
   several proofs of Cantor's theorem using TLA+'s
   hierarchical proof language

consensus/PaxosProof.tla
   high level specification of Consensus with two
   refinements implementing an abstract Paxos algorithm
   (incomplete and largely superseded by paxos/)

data/*.tla
   various theorems on sets, sequences and graphs (incomplete)
