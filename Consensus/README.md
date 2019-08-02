# Consensus

## [`Consensus.tla`]()

## [`Voting.tla`](https://github.com/hengxin/tlaps-examples/blob/master/Consensus/Voting.tla)
`Voting` models the behaviors of Acceptors in Paxos.

Each acceptor `a` can either `IncreaseMaxBal(a, b)` or `VoteFor(a, b, v)`.

In `IncreaseMaxBal(a, b)`, the acceptor `a` makes promise that it will not ever accept ballots 
numbered less than `b`.

In `VoteFor(a, b, v)`, the acceptor `a` first checks whether the ballot `<<b, v>>` 
is safe to accept (by `ShowsSafeAt(Q, b, v)`) and if so accepts it.

---
For the correctness, it is crucial to show the `VotesSafe` property,
which states that every vote is indeed safe (`SafeAt(b, v)`).

- `THEOREM ShowsSafety`

## [`PaxosTuple.tla`]()

## [`PaxosProof.tla`]()
