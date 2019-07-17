(* automatically generated -- do not edit manually *)
theory Voting imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'1:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsBijection suppressed *)
(* usable definition IsFiniteSet suppressed *)
fixes Cardinality
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition TypeOK suppressed *)
(* usable definition DidNotVoteAt suppressed *)
(* usable definition ShowsSafeAt suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition CannotVoteAt suppressed *)
(* usable definition NoneOtherChoosableAt suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition VotesSafe suppressed *)
(* usable definition OneVote suppressed *)
(* usable definition OneValuePerBallot suppressed *)
(* usable definition Inv suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!NatInductiveDefHypothesis suppressed *)
(* usable definition C!NatInductiveDefConclusion suppressed *)
(* usable definition C!FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition C!FiniteNatInductiveDefConclusion suppressed *)
(* usable definition C!IsBijection suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!Inv suppressed *)
assumes v'136: "((\<forall> Q \<in> (Quorum) : (((Q) \<subseteq> (Acceptor)))) & (\<forall> a_Q1a \<in> (Quorum) : (\<forall> a_Q2a \<in> (Quorum) : (((((a_Q1a) \<inter> (a_Q2a))) \<noteq> ({}))))))"
assumes v'137: "(\<forall>S : (\<forall>T : (((\<forall>x : (((((x) \<in> (S))) \<Leftrightarrow> (((x) \<in> (T)))))) \<Rightarrow> (((S) = (T)))))))"
shows "((((((votes) = ([ a \<in> (Acceptor)  \<mapsto> ({})]))) & (((maxBal) = ([ a \<in> (Acceptor)  \<mapsto> ((minus (((Succ[0])))))])))) \<Rightarrow> (((subsetOf((Value), %v. (\<exists> b \<in> (Ballot) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((<<(b), (v)>>) \<in> (fapply ((votes), (a)))))))))) = ({})))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"
using assms by force
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end
