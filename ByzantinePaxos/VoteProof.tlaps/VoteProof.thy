(* automatically generated -- do not edit manually *)
theory VoteProof imports Constant Zenon begin
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

lemma ob'3:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
fixes v
assumes v_in : "(v \<in> (Value))"
assumes v'38: "(\<forall>b : (((fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((((bb) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (bb))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((SA), (a_ca))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))))]))))), (b))) = (fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((((bb) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (bb))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((SA), (a_ca))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))))]))))), (b))))))"
assumes v'39: "(\<forall> b \<in> (Nat) : (((fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((((bb) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (bb))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((SA), (a_ca))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))))]))))), (b))) = ((((b) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (b))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((((bb) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply ((maxBal), (a))), (bb))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((SA), (a_ca_1))) & (\<forall> a \<in> (Q_1) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((DidNotVoteIn ((a), (d)))))))))))]))))), (a_ca))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d))))))))))))))"
shows "(\<forall> b \<in> (Nat) : (((fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((((bb) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (bb))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((SA), (a_ca))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))))]))))), (b))) = ((((b) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (b))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((((bb) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply ((maxBal), (a))), (bb))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((SA), (a_ca_1))) & (\<forall> a \<in> (Q_1) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((DidNotVoteIn ((a), (d)))))))))))]))))), (a_ca))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d))))))))))))))"(is "PROP ?ob'3")
proof -
ML_command {* writeln "*** TLAPS ENTER 3"; *}
show "PROP ?ob'3"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_ff2c00.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_ff2c00.znn.out
;; obligation #3
$hyp "v_in" (TLA.in v Value)
$hyp "v'38" (A. ((b) (= (TLA.fapply (t. ((SA) (= SA
(TLA.Fcn arith.N ((bb) (\/ (= bb 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le bb
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (TLA.fapply SA a_ca)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))))))))) b) (TLA.fapply (t. ((SA) (= SA
(TLA.Fcn arith.N ((bb) (\/ (= bb 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le bb
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (TLA.fapply SA a_ca)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))))))))) b))))
$hyp "v'39" (TLA.bAll arith.N ((b) (= (TLA.fapply (t. ((SA) (= SA
(TLA.Fcn arith.N ((bb) (\/ (= bb 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le bb
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (TLA.fapply SA a_ca)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))))))))) b) (\/ (= b 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le b
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (TLA.fapply (t. ((SA) (= SA
(TLA.Fcn arith.N ((bb) (\/ (= bb 0)
(TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le bb
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (TLA.fapply SA a_ca_1)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca_1 w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q_1 ((a) (DidNotVoteIn a
d))))))))))))))))) a_ca)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d)))))))))))))))
$goal (TLA.bAll arith.N ((b) (= (TLA.fapply (t. ((SA) (= SA
(TLA.Fcn arith.N ((bb) (\/ (= bb 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le bb
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (TLA.fapply SA a_ca)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))))))))) b) (\/ (= b 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le b
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (TLA.fapply (t. ((SA) (= SA
(TLA.Fcn arith.N ((bb) (\/ (= bb 0)
(TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le bb
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (TLA.fapply SA a_ca_1)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca_1 w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add bb
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q_1 ((a) (DidNotVoteIn a
d))))))))))))))))) a_ca)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d)))))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hc:"bAll(Nat, (\<lambda>b. (((CHOOSE SA:(SA=Fcn(Nat, (\<lambda>bb. ((bb=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (bb <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (bb +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>((SA[a_ca])&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (bb +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))[b])=((b=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(((CHOOSE SA:(SA=Fcn(Nat, (\<lambda>bb. ((bb=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (bb <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (bb +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>((SA[a_ca])&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (bb +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))[a_ca])&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))" (is "?z_hc")
 using v'39 by blast
 assume z_Hd:"(~?z_hc)"
 show FALSE
 by (rule notE [OF z_Hd z_Hc])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 3"; *} qed
lemma ob'6:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
assumes v'33: "((\<And> v :: c. v \<in> (Value) \<Longrightarrow> (\<forall> b \<in> (Ballot) : ((((SafeAt ((b), (v)))) = ((((b) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (b))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d))))))))))))))))"
shows "(\<forall> b \<in> (Ballot) : (\<forall> v \<in> (Value) : ((((SafeAt ((b), (v)))) = ((((b) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (b))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))))))))"(is "PROP ?ob'6")
proof -
ML_command {* writeln "*** TLAPS ENTER 6"; *}
show "PROP ?ob'6"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_fb9897.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_fb9897.znn.out
;; obligation #6
$hyp "v'33" (TLA.bAll Value ((v) (TLA.bAll Ballot ((b) (= (SafeAt b v)
(\/ (= b 0) (TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le b
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d)))))))))))))))))
$goal (TLA.bAll Ballot ((b) (TLA.bAll Value ((v) (= (SafeAt b v) (\/ (= b 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le b
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d)))))))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"bAll(Value, (\<lambda>v. bAll(Ballot, (\<lambda>b. (SafeAt(b, v)=((b=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))" (is "?z_ha")
 using v'33 by blast
 assume z_Hb:"(~bAll(Ballot, (\<lambda>b. bAll(Value, (\<lambda>v. (SafeAt(b, v)=((b=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))" (is "~?z_hcb")
 have z_Hcf_z_Ha: "(\\A x:((x \\in Value)=>bAll(Ballot, (\<lambda>b. (SafeAt(b, x)=((b=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))) == ?z_ha" (is "?z_hcf == _")
 by (unfold bAll_def)
 have z_Hcf: "?z_hcf" (is "\\A x : ?z_hdd(x)")
 by (unfold z_Hcf_z_Ha, fact z_Ha)
 have z_Hde_z_Hb: "(~(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) == (~?z_hcb)" (is "?z_hde == ?z_hb")
 by (unfold bAll_def)
 have z_Hde: "?z_hde" (is "~(\\A x : ?z_heb(x))")
 by (unfold z_Hde_z_Hb, fact z_Hb)
 have z_Hec: "(\\E x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))" (is "\\E x : ?z_hee(x)")
 by (rule zenon_notallex_0 [of "?z_heb", OF z_Hde])
 have z_Hef: "?z_hee((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))))" (is "~(?z_heh=>?z_hei)")
 by (rule zenon_ex_choose_0 [of "?z_hee", OF z_Hec])
 have z_Heh: "?z_heh"
 by (rule zenon_notimply_0 [OF z_Hef])
 have z_Hej: "(~?z_hei)"
 by (rule zenon_notimply_1 [OF z_Hef])
 have z_Hek_z_Hej: "(~(\\A x:((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))) == (~?z_hei)" (is "?z_hek == ?z_hej")
 by (unfold bAll_def)
 have z_Hek: "?z_hek" (is "~(\\A x : ?z_hfe(x))")
 by (unfold z_Hek_z_Hej, fact z_Hej)
 have z_Hff: "(\\E x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))" (is "\\E x : ?z_hfh(x)")
 by (rule zenon_notallex_0 [of "?z_hfe", OF z_Hek])
 have z_Hfi: "?z_hfh((CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))" (is "~(?z_hfk=>?z_hfl)")
 by (rule zenon_ex_choose_0 [of "?z_hfh", OF z_Hff])
 have z_Hfk: "?z_hfk"
 by (rule zenon_notimply_0 [OF z_Hfi])
 have z_Hfm: "(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), (CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))~=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, (CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=(CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))" (is "?z_hfn~=?z_hfo")
 by (rule zenon_notimply_1 [OF z_Hfi])
 have z_Hge: "?z_hdd((CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))" (is "_=>?z_hgf")
 by (rule zenon_all_0 [of "?z_hdd" "(CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))", OF z_Hcf])
 show FALSE
 proof (rule zenon_imply [OF z_Hge])
  assume z_Hgg:"(~?z_hfk)"
  show FALSE
  by (rule notE [OF z_Hgg z_Hfk])
 next
  assume z_Hgf:"?z_hgf"
  have z_Hgh_z_Hgf: "(\\A x:((x \\in Ballot)=>(SafeAt(x, (CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, (CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=(CHOOSE x:(~((x \\in Value)=>(SafeAt((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))), x)=(((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), ((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))) == ?z_hgf" (is "?z_hgh == _")
  by (unfold bAll_def)
  have z_Hgh: "?z_hgh" (is "\\A x : ?z_hgs(x)")
  by (unfold z_Hgh_z_Hgf, fact z_Hgf)
  have z_Hgt: "?z_hgs((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))))"
  by (rule zenon_all_0 [of "?z_hgs" "(CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))))", OF z_Hgh])
  show FALSE
  proof (rule zenon_imply [OF z_Hgt])
   assume z_Hgu:"(~?z_heh)"
   show FALSE
   by (rule notE [OF z_Hgu z_Heh])
  next
   assume z_Hfl:"?z_hfl"
   show FALSE
   by (rule notE [OF z_Hfm z_Hfl])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 6"; *} qed
lemma ob'24:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
fixes v
assumes v_in : "(v \<in> (Value))"
(* usable definition Def suppressed *)
assumes v'41: "(((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((Def ((SA), (bb))))]))))) = ([ b \<in> (Nat)  \<mapsto> ((Def ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((Def ((SA), (bb))))]))))), (b))))])))"
shows "(\<forall> b \<in> (Nat) : (((fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((Def ((SA), (bb))))]))))), (b))) = ((Def ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((Def ((SA), (bb))))]))))), (b)))))))"(is "PROP ?ob'24")
proof -
ML_command {* writeln "*** TLAPS ENTER 24"; *}
show "PROP ?ob'24"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_9aa3e6.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_9aa3e6.znn.out
;; obligation #24
$hyp "v_in" (TLA.in v Value)
$hyp "v'41" (= (t. ((SA) (= SA (TLA.Fcn arith.N ((bb) (Def SA bb))))))
(TLA.Fcn arith.N ((b) (Def (t. ((SA) (= SA (TLA.Fcn arith.N ((bb) (Def SA
bb)))))) b))))
$goal (TLA.bAll arith.N ((b) (= (TLA.fapply (t. ((SA) (= SA
(TLA.Fcn arith.N ((bb) (Def SA bb)))))) b) (Def (t. ((SA) (= SA
(TLA.Fcn arith.N ((bb) (Def SA bb))))))
b))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"((CHOOSE SA:(SA=Fcn(Nat, (\<lambda>bb. Def(SA, bb)))))=Fcn(Nat, (\<lambda>b. Def((CHOOSE SA:(SA=Fcn(Nat, (\<lambda>bb. Def(SA, bb))))), b))))" (is "?z_hd=?z_hl")
 using v'41 by blast
 assume z_Hc:"(~bAll(Nat, (\<lambda>b. ((?z_hd[b])=Def(?z_hd, b)))))" (is "~?z_hp")
 have z_Ht_z_Hc: "(~(\\A x:((x \\in Nat)=>((?z_hd[x])=Def(?z_hd, x))))) == (~?z_hp)" (is "?z_ht == ?z_hc")
 by (unfold bAll_def)
 have z_Ht: "?z_ht" (is "~(\\A x : ?z_hbb(x))")
 by (unfold z_Ht_z_Hc, fact z_Hc)
 have z_Hbc: "(\\E x:(~((x \\in Nat)=>((?z_hd[x])=Def(?z_hd, x)))))" (is "\\E x : ?z_hbe(x)")
 by (rule zenon_notallex_0 [of "?z_hbb", OF z_Ht])
 have z_Hbf: "?z_hbe((CHOOSE x:(~((x \\in Nat)=>((?z_hd[x])=Def(?z_hd, x))))))" (is "~(?z_hbh=>?z_hbi)")
 by (rule zenon_ex_choose_0 [of "?z_hbe", OF z_Hbc])
 have z_Hbh: "?z_hbh"
 by (rule zenon_notimply_0 [OF z_Hbf])
 have z_Hbj: "((?z_hd[(CHOOSE x:(~((x \\in Nat)=>((?z_hd[x])=Def(?z_hd, x)))))])~=Def(?z_hd, (CHOOSE x:(~((x \\in Nat)=>((?z_hd[x])=Def(?z_hd, x)))))))" (is "?z_hbk~=?z_hbl")
 by (rule zenon_notimply_1 [OF z_Hbf])
 have z_Hbm: "(((isAFcn(?z_hd)<=>isAFcn(?z_hl))&(DOMAIN(?z_hd)=DOMAIN(?z_hl)))&(\\A zenon_Vh:((?z_hd[zenon_Vh])=(?z_hl[zenon_Vh]))))" (is "?z_hbn&?z_hbu")
 by (rule zenon_funequal_0 [of "?z_hd" "?z_hl", OF z_Hb])
 have z_Hbu: "?z_hbu" (is "\\A x : ?z_hbz(x)")
 by (rule zenon_and_1 [OF z_Hbm])
 have z_Hca: "?z_hbz((CHOOSE x:(~((x \\in Nat)=>((?z_hd[x])=Def(?z_hd, x))))))" (is "_=?z_hcb")
 by (rule zenon_all_0 [of "?z_hbz" "(CHOOSE x:(~((x \\in Nat)=>((?z_hd[x])=Def(?z_hd, x)))))", OF z_Hbu])
 show FALSE
 proof (rule notE [OF z_Hbj])
  have z_Hcc: "(?z_hcb=?z_hbl)"
  proof (rule zenon_nnpp [of "(?z_hcb=?z_hbl)"])
   assume z_Hcd:"(?z_hcb~=?z_hbl)"
   show FALSE
   proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vn. (zenon_Vn~=?z_hbl))" "Nat" "(\<lambda>b. Def(?z_hd, b))" "(CHOOSE x:(~((x \\in Nat)=>((?z_hd[x])=Def(?z_hd, x)))))", OF z_Hcd])
    assume z_Hch:"(~?z_hbh)"
    show FALSE
    by (rule notE [OF z_Hch z_Hbh])
   next
    assume z_Hci:"(?z_hbl~=?z_hbl)"
    show FALSE
    by (rule zenon_noteq [OF z_Hci])
   qed
  qed
  have z_Hbi: "?z_hbi"
  by (rule subst [where P="(\<lambda>zenon_Vxb. (?z_hbk=zenon_Vxb))", OF z_Hcc], fact z_Hca)
  thus "?z_hbi" .
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 24"; *} qed
lemma ob'91:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
assumes v'39: "(TypeOK)"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> ((isa_peri_peri_a (((0)), (b)))))"
assumes v'60: "((((SafeAt (((arith_add ((b), ((Succ[0]))))), (v)))) = (((((arith_add ((b), ((Succ[0]))))) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), ((arith_add ((b), ((Succ[0]))))))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))))))"
assumes v'61: "(((((((arith_add ((b), ((Succ[0]))))) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), ((arith_add ((b), ((Succ[0]))))))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d))))))))))) = (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), ((arith_add ((b), ((Succ[0]))))))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d))))))))))))"
assumes v'62: "(((\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), ((arith_add ((b), ((Succ[0]))))))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))) = (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), ((arith_add ((b), ((Succ[0]))))))))) & (\<exists> cc \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), (b)))) : ((((((cc) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((cc), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (cc), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((cc), ((Succ[0]))))), (b)))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d))))))))))))"
assumes v'63: "((SafeAt (((arith_add ((b), ((Succ[0]))))), (v))))"
shows "(\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), ((arith_add ((b), ((Succ[0]))))))))) & (\<exists> cc \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), (b)))) : ((((((cc) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((cc), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (cc), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((cc), ((Succ[0]))))), (b)))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d))))))))))"(is "PROP ?ob'91")
proof -
ML_command {* writeln "*** TLAPS ENTER 91"; *}
show "PROP ?ob'91"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_345d4f.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_345d4f.znn.out
;; obligation #91
$hyp "v'39" TypeOK
$hyp "b_in" (TLA.in b Ballot)
$hyp "v_in" (TLA.in v Value)
$hyp "a_ca_in" (TLA.in a_ca (arith.intrange 0
b))
$hyp "v'60" (= (SafeAt (arith.add b (TLA.fapply TLA.Succ 0)) v)
(\/ (= (arith.add b (TLA.fapply TLA.Succ 0)) 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le (arith.add b
(TLA.fapply TLA.Succ 0)) (TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca_1 w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d)))))))))))))
$hyp "v'61" (= (\/ (= (arith.add b (TLA.fapply TLA.Succ 0)) 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le (arith.add b
(TLA.fapply TLA.Succ 0)) (TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca_1 w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))))
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le (arith.add b
(TLA.fapply TLA.Succ 0)) (TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca_1 w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))))
$hyp "v'62" (= (TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le (arith.add b
(TLA.fapply TLA.Succ 0)) (TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca_1 w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))) (TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le (arith.add b
(TLA.fapply TLA.Succ 0)) (TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
b) ((cc) (/\ (=> (-. (= cc (arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (SafeAt cc v) (TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a cc w)
(= w v)))))))) (TLA.bAll (arith.intrange (arith.add cc
(TLA.fapply TLA.Succ 0)) b) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))))
$hyp "v'63" (SafeAt (arith.add b (TLA.fapply TLA.Succ 0))
v)
$goal (TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le (arith.add b
(TLA.fapply TLA.Succ 0)) (TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
b) ((cc) (/\ (=> (-. (= cc (arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (SafeAt cc v) (TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a cc w)
(= w v)))))))) (TLA.bAll (arith.intrange (arith.add cc
(TLA.fapply TLA.Succ 0)) b) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d)))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"((((b + 1)=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((b + 1) +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca_1, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), ((b + 1) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))=bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((b + 1) +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca_1, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), ((b + 1) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))" (is "?z_hj=?z_hp")
 using v'61 by blast
 have z_Hh:"SafeAt((b + 1), v)" (is "?z_hh")
 using v'63 by blast
 have z_He:"(?z_hh=?z_hj)"
 using v'60 by blast
 have z_Hg:"(?z_hp=bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), b), (\<lambda>cc. (((cc~= -.(1))=>(SafeAt(cc, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, cc, w)=>(w=v))))))))&bAll(isa'dotdot((cc + 1), b), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))" (is "_=?z_hcd")
 using v'62 by blast
 have zenon_L1_: "(TRUE=(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), b), (\<lambda>cc. (((cc~= -.(1))=>(SafeAt(cc, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, cc, w)=>(w=v))))))))&bAll(isa'dotdot((cc + 1), b), (\<lambda>d. bAll(x, (\<lambda>a. DidNotVoteIn(a, d)))))))))))) ==> (~(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), b), (\<lambda>cc. (((cc~= -.(1))=>(SafeAt(cc, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, cc, w)=>(w=v))))))))&bAll(isa'dotdot((cc + 1), b), (\<lambda>d. bAll(x, (\<lambda>a. DidNotVoteIn(a, d)))))))))))) ==> FALSE" (is "?z_hcy ==> ?z_hdp ==> FALSE")
 proof -
  assume z_Hcy:"?z_hcy" (is "?z_hcz=?z_hda")
  assume z_Hdp:"?z_hdp" (is "~(\\E x : ?z_hdq(x))")
  have z_Hda: "?z_hda"
  by (rule zenon_eq_true_x_0 [of "?z_hda", OF z_Hcy])
  show FALSE
  by (rule notE [OF z_Hdp z_Hda])
 qed
 assume z_Hi:"(~?z_hcd)"
 have z_Hdr_z_Hf: "(?z_hj=(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((b + 1) +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca_1, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), ((b + 1) +  -.(1))), (\<lambda>d. bAll(x, (\<lambda>a. DidNotVoteIn(a, d)))))))))))) == (?z_hj=?z_hp)" (is "?z_hdr == ?z_hf")
 by (unfold bEx_def)
 have z_Hdr: "?z_hdr" (is "_=?z_hds")
 by (unfold z_Hdr_z_Hf, fact z_Hf)
 have z_Hec_z_Hg: "(?z_hds=?z_hcd) == (?z_hp=?z_hcd)" (is "?z_hec == ?z_hg")
 by (unfold bEx_def)
 have z_Hec: "?z_hec"
 by (unfold z_Hec_z_Hg, fact z_Hg)
 have z_Hed_z_Hec: "(?z_hds=(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), b), (\<lambda>cc. (((cc~= -.(1))=>(SafeAt(cc, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, cc, w)=>(w=v))))))))&bAll(isa'dotdot((cc + 1), b), (\<lambda>d. bAll(x, (\<lambda>a. DidNotVoteIn(a, d)))))))))))) == ?z_hec" (is "?z_hed == _")
 by (unfold bEx_def)
 have z_Hed: "?z_hed" (is "_=?z_hda")
 by (unfold z_Hed_z_Hec, fact z_Hec)
 have z_Hdp_z_Hi: "(~?z_hda) == (~?z_hcd)" (is "?z_hdp == ?z_hi")
 by (unfold bEx_def)
 have z_Hdp: "?z_hdp" (is "~(\\E x : ?z_hdq(x))")
 by (unfold z_Hdp_z_Hi, fact z_Hi)
 have z_Hee: "(TRUE=?z_hj)" (is "?z_hcz=_")
 by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vj. (zenon_Vj=?z_hj))" "?z_hh", OF z_He z_Hh])
 have z_Hj: "?z_hj" (is "?z_hk|_")
 by (rule zenon_eq_true_x_0 [of "?z_hj", OF z_Hee])
 show FALSE
 proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vt. (zenon_Vt=?z_hda))" "(\<lambda>x. ((x \\in Quorum)&(bAll(x, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((b + 1) +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca_1, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), ((b + 1) +  -.(1))), (\<lambda>d. bAll(x, (\<lambda>a. DidNotVoteIn(a, d)))))))))))", OF z_Hed])
  assume z_Hem:"(?z_hds=?z_hcz)"
  assume z_Hcy:"(?z_hcz=?z_hda)"
  show FALSE
  by (rule zenon_L1_ [OF z_Hcy z_Hdp])
 next
  assume z_Hen:"(?z_hds=FALSE)" (is "_=?z_heo")
  assume z_Hep:"(?z_heo=?z_hda)"
  have z_Heq: "(~?z_hds)" (is "~(\\E x : ?z_hel(x))")
  by (rule zenon_eq_x_false_0 [of "?z_hds", OF z_Hen])
  show FALSE
  proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vr. (zenon_Vr=?z_hds))" "?z_hk" "?z_hp", OF z_Hdr])
   assume z_Heu:"(?z_hj=?z_hcz)"
   assume z_Hev:"(?z_hcz=?z_hds)"
   have z_Hds: "?z_hds"
   by (rule zenon_eq_true_x_0 [of "?z_hds", OF z_Hev])
   show FALSE
   by (rule notE [OF z_Heq z_Hds])
  next
   assume z_Hew:"(?z_hj=?z_heo)"
   assume z_Hex:"(?z_heo=?z_hds)"
   have z_Hey: "(~?z_hj)"
   by (rule zenon_eq_x_false_0 [of "?z_hj", OF z_Hew])
   show FALSE
   by (rule notE [OF z_Hey z_Hj])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 91"; *} qed
lemma ob'98:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
assumes v'39: "(TypeOK)"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> ((isa_peri_peri_a (((0)), (b)))))"
assumes v'59: "(\<forall> b_1 \<in> (Ballot) : (\<forall> v_1 \<in> (Value) : ((((SafeAt ((b_1), (v_1)))) = ((((b_1) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (b_1))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (v_1)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w)))) \<Rightarrow> (((w) = (v_1)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))))))))"
assumes v'60: "((((arith_add ((b), ((Succ[0]))))) \<in> (Ballot)))"
assumes v'61: "((((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0])))))))) = (b)))"
shows "((((SafeAt (((arith_add ((b), ((Succ[0]))))), (v)))) = (((((arith_add ((b), ((Succ[0]))))) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), ((arith_add ((b), ((Succ[0]))))))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))))))"(is "PROP ?ob'98")
proof -
ML_command {* writeln "*** TLAPS ENTER 98"; *}
show "PROP ?ob'98"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_d9f6da.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_d9f6da.znn.out
;; obligation #98
$hyp "v'39" TypeOK
$hyp "b_in" (TLA.in b Ballot)
$hyp "v_in" (TLA.in v Value)
$hyp "a_ca_in" (TLA.in a_ca (arith.intrange 0
b))
$hyp "v'59" (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v_1) (= (SafeAt b_1
v_1) (\/ (= b_1 0) (TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le b_1
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 v_1)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca_1 w) (= w
v_1)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d)))))))))))))))))
$hyp "v'60" (TLA.in (arith.add b (TLA.fapply TLA.Succ 0))
Ballot)
$hyp "v'61" (= (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0))) b)
$goal (= (SafeAt (arith.add b (TLA.fapply TLA.Succ 0)) v) (\/ (= (arith.add b
(TLA.fapply TLA.Succ 0)) 0)
(TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le (arith.add b
(TLA.fapply TLA.Succ 0)) (TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca_1 w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d)))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v_1. (SafeAt(b_1, v_1)=((b_1=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (b_1 <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b_1 +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v_1)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca_1, w)=>(w=v_1))))))))&bAll(isa'dotdot((a_ca_1 + 1), (b_1 +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))" (is "?z_he")
 using v'59 by blast
 have z_Hc:"(v \\in Value)" (is "?z_hc")
 using v_in by blast
 have z_Hf:"((b + 1) \\in Ballot)" (is "?z_hf")
 using v'60 by blast
 assume z_Hh:"(SafeAt((b + 1), v)~=(((b + 1)=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((b + 1) +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca_1, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), ((b + 1) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))" (is "?z_hck~=?z_hcl")
 have z_Hdj_z_He: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v_1. (SafeAt(x, v_1)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v_1)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca_1, w)=>(w=v_1))))))))&bAll(isa'dotdot((a_ca_1 + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))) == ?z_he" (is "?z_hdj == _")
 by (unfold bAll_def)
 have z_Hdj: "?z_hdj" (is "\\A x : ?z_heg(x)")
 by (unfold z_Hdj_z_He, fact z_He)
 have z_Heh: "?z_heg((b + 1))" (is "_=>?z_hei")
 by (rule zenon_all_0 [of "?z_heg" "(b + 1)", OF z_Hdj])
 show FALSE
 proof (rule zenon_imply [OF z_Heh])
  assume z_Hej:"(~?z_hf)"
  show FALSE
  by (rule notE [OF z_Hej z_Hf])
 next
  assume z_Hei:"?z_hei"
  have z_Hek_z_Hei: "(\\A x:((x \\in Value)=>(SafeAt((b + 1), x)=(((b + 1)=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. ((b + 1) <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), ((b + 1) +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca_1, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca_1 + 1), ((b + 1) +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))) == ?z_hei" (is "?z_hek == _")
  by (unfold bAll_def)
  have z_Hek: "?z_hek" (is "\\A x : ?z_hff(x)")
  by (unfold z_Hek_z_Hei, fact z_Hei)
  have z_Hfg: "?z_hff(v)" (is "_=>?z_hfh")
  by (rule zenon_all_0 [of "?z_hff" "v", OF z_Hek])
  show FALSE
  proof (rule zenon_imply [OF z_Hfg])
   assume z_Hfi:"(~?z_hc)"
   show FALSE
   by (rule notE [OF z_Hfi z_Hc])
  next
   assume z_Hfh:"?z_hfh"
   show FALSE
   by (rule notE [OF z_Hh z_Hfh])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 98"; *} qed
lemma ob'186:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
assumes v'44: "(TypeOK)"
assumes v'45: "(a_VInv1a)"
assumes v'46: "(a_VInv2a)"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes w
assumes w_in : "(w \<in> (Value))"
assumes v'54: "(((((0)) \<in> (Ballot))) & (\<forall> a_ca \<in> (Ballot) : ((~ ((greater (((0)), (a_ca))))))))"
shows "(fapply (([ b \<in> (Ballot)  \<mapsto> (\<forall> a_ca \<in> (Ballot) : ((((((((greater ((b), (a_ca)))) \<and> ((SafeAt ((b), (v)))))) \<and> ((ChosenIn ((a_ca), (w)))))) \<Rightarrow> (((v) = (w))))))]), ((0))))"(is "PROP ?ob'186")
proof -
ML_command {* writeln "*** TLAPS ENTER 186"; *}
show "PROP ?ob'186"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_37be25.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_37be25.znn.out
;; obligation #186
$hyp "v'44" TypeOK
$hyp "v'45" a_VInv1a
$hyp "v'46" a_VInv2a
$hyp "v_in" (TLA.in v Value)
$hyp "w_in" (TLA.in w Value)
$hyp "v'54" (/\ (TLA.in 0 Ballot) (TLA.bAll Ballot ((a_ca) (-. (arith.lt a_ca
0)))))
$goal (TLA.fapply (TLA.Fcn Ballot ((b) (TLA.bAll Ballot ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b) (SafeAt b v)) (ChosenIn a_ca w)) (= v
w)))))) 0)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"((0 \\in Ballot)&bAll(Ballot, (\<lambda>a_ca. (~(a_ca < 0)))))" (is "?z_hh&?z_hk")
 using v'54 by blast
 assume z_Hg:"(~(Fcn(Ballot, (\<lambda>b. bAll(Ballot, (\<lambda>a_ca. ((((a_ca < b)&SafeAt(b, v))&ChosenIn(a_ca, w))=>(v=w))))))[0]))" (is "~?z_hp")
 have z_Hh: "?z_hh"
 by (rule zenon_and_0 [OF z_Hf])
 have z_Hk: "?z_hk"
 by (rule zenon_and_1 [OF z_Hf])
 have z_Hbe_z_Hk: "(\\A x:((x \\in Ballot)=>(~(x < 0)))) == ?z_hk" (is "?z_hbe == _")
 by (unfold bAll_def)
 have z_Hbe: "?z_hbe" (is "\\A x : ?z_hbk(x)")
 by (unfold z_Hbe_z_Hk, fact z_Hk)
 show FALSE
 proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vf. (~zenon_Vf))" "Ballot" "(\<lambda>b. bAll(Ballot, (\<lambda>a_ca. ((((a_ca < b)&SafeAt(b, v))&ChosenIn(a_ca, w))=>(v=w)))))" "0", OF z_Hg])
  assume z_Hbo:"(~?z_hh)"
  show FALSE
  by (rule notE [OF z_Hbo z_Hh])
 next
  assume z_Hbp:"(~bAll(Ballot, (\<lambda>a_ca. ((((a_ca < 0)&SafeAt(0, v))&ChosenIn(a_ca, w))=>(v=w)))))" (is "~?z_hbq")
  have z_Hbw_z_Hbp: "(~(\\A x:((x \\in Ballot)=>((((x < 0)&SafeAt(0, v))&ChosenIn(x, w))=>(v=w))))) == (~?z_hbq)" (is "?z_hbw == ?z_hbp")
  by (unfold bAll_def)
  have z_Hbw: "?z_hbw" (is "~(\\A x : ?z_hcd(x))")
  by (unfold z_Hbw_z_Hbp, fact z_Hbp)
  have z_Hce: "(\\E x:(~((x \\in Ballot)=>((((x < 0)&SafeAt(0, v))&ChosenIn(x, w))=>(v=w)))))" (is "\\E x : ?z_hcg(x)")
  by (rule zenon_notallex_0 [of "?z_hcd", OF z_Hbw])
  have z_Hch: "?z_hcg((CHOOSE x:(~((x \\in Ballot)=>((((x < 0)&SafeAt(0, v))&ChosenIn(x, w))=>(v=w))))))" (is "~(?z_hcj=>?z_hck)")
  by (rule zenon_ex_choose_0 [of "?z_hcg", OF z_Hce])
  have z_Hcj: "?z_hcj"
  by (rule zenon_notimply_0 [OF z_Hch])
  have z_Hcl: "(~?z_hck)" (is "~(?z_hcm=>?z_hbd)")
  by (rule zenon_notimply_1 [OF z_Hch])
  have z_Hcm: "?z_hcm" (is "?z_hcn&?z_hco")
  by (rule zenon_notimply_0 [OF z_Hcl])
  have z_Hcn: "?z_hcn" (is "?z_hcp&?z_hbv")
  by (rule zenon_and_0 [OF z_Hcm])
  have z_Hcp: "?z_hcp"
  by (rule zenon_and_0 [OF z_Hcn])
  have z_Hcq: "?z_hbk((CHOOSE x:(~((x \\in Ballot)=>((((x < 0)&?z_hbv)&ChosenIn(x, w))=>?z_hbd)))))" (is "_=>?z_hcr")
  by (rule zenon_all_0 [of "?z_hbk" "(CHOOSE x:(~((x \\in Ballot)=>((((x < 0)&?z_hbv)&ChosenIn(x, w))=>?z_hbd))))", OF z_Hbe])
  show FALSE
  proof (rule zenon_imply [OF z_Hcq])
   assume z_Hcs:"(~?z_hcj)"
   show FALSE
   by (rule notE [OF z_Hcs z_Hcj])
  next
   assume z_Hcr:"?z_hcr"
   show FALSE
   by (rule notE [OF z_Hcr z_Hcp])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 186"; *} qed
lemma ob'50:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
fixes f
fixes n
assumes n_in : "(n \<in> (Nat))"
assumes v'48: "(fapply (([ m \<in> (Nat)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (m)))) : (fapply ((f), (j))))]), ((0))))"
assumes v'49: "((\<And> k :: c. k \<in> (Nat) \<Longrightarrow> ((fapply (([ m \<in> (Nat)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (m)))) : (fapply ((f), (j))))]), (k))) \<Longrightarrow> (fapply (([ m \<in> (Nat)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (m)))) : (fapply ((f), (j))))]), ((arith_add ((k), ((Succ[0]))))))))))"
assumes v'50: "(\<forall>f_1 : ((((fapply ((f_1), ((0)))) & (\<forall> n_1 \<in> (Nat) : (((fapply ((f_1), (n_1))) \<Rightarrow> (fapply ((f_1), ((arith_add ((n_1), ((Succ[0]))))))))))) \<Rightarrow> (\<forall> n_1 \<in> (Nat) : (fapply ((f_1), (n_1)))))))"
shows "(\<forall> k \<in> (Nat) : (fapply (([ m \<in> (Nat)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (m)))) : (fapply ((f), (j))))]), (k))))"(is "PROP ?ob'50")
proof -
ML_command {* writeln "*** TLAPS ENTER 50"; *}
show "PROP ?ob'50"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_cccbb6.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_cccbb6.znn.out
;; obligation #50
$hyp "n_in" (TLA.in n arith.N)
$hyp "v'48" (TLA.fapply (TLA.Fcn arith.N ((m) (TLA.bAll (arith.intrange 0
m) ((j) (TLA.fapply f j))))) 0)
$hyp "v'49" (TLA.bAll arith.N ((k) (=> (TLA.fapply (TLA.Fcn arith.N ((m) (TLA.bAll (arith.intrange 0
m) ((j) (TLA.fapply f j))))) k) (TLA.fapply (TLA.Fcn arith.N ((m) (TLA.bAll (arith.intrange 0
m) ((j) (TLA.fapply f j))))) (arith.add k
(TLA.fapply TLA.Succ 0))))))
$hyp "v'50" (A. ((f_1) (=> (/\ (TLA.fapply f_1 0)
(TLA.bAll arith.N ((n_1) (=> (TLA.fapply f_1 n_1)
(TLA.fapply f_1 (arith.add n_1 (TLA.fapply TLA.Succ 0)))))))
(TLA.bAll arith.N ((n_1) (TLA.fapply f_1 n_1))))))
$goal (TLA.bAll arith.N ((k) (TLA.fapply (TLA.Fcn arith.N ((m) (TLA.bAll (arith.intrange 0
m) ((j) (TLA.fapply f j))))) k)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(\\A f_1:(((f_1[0])&bAll(Nat, (\<lambda>n_1. ((f_1[n_1])=>(f_1[(n_1 + 1)])))))=>bAll(Nat, (\<lambda>n_1. (f_1[n_1])))))" (is "\\A x : ?z_hv(x)")
 using v'50 by blast
 have z_Hb:"(Fcn(Nat, (\<lambda>m. bAll(isa'dotdot(0, m), (\<lambda>j. (f[j])))))[0])" (is "?z_hb")
 using v'48 by blast
 have z_Hc:"bAll(Nat, (\<lambda>k. ((Fcn(Nat, (\<lambda>m. bAll(isa'dotdot(0, m), (\<lambda>j. (f[j])))))[k])=>(Fcn(Nat, (\<lambda>m. bAll(isa'dotdot(0, m), (\<lambda>j. (f[j])))))[(k + 1)]))))" (is "?z_hc")
 using v'49 by blast
 assume z_He:"(~bAll(Nat, (\<lambda>k. (Fcn(Nat, (\<lambda>m. bAll(isa'dotdot(0, m), (\<lambda>j. (f[j])))))[k]))))" (is "~?z_hbl")
 have z_Hbn: "?z_hv(Fcn(Nat, (\<lambda>m. bAll(isa'dotdot(0, m), (\<lambda>j. (f[j]))))))" (is "?z_hbo=>_")
 by (rule zenon_all_0 [of "?z_hv" "Fcn(Nat, (\<lambda>m. bAll(isa'dotdot(0, m), (\<lambda>j. (f[j])))))", OF z_Hd])
 show FALSE
 proof (rule zenon_imply [OF z_Hbn])
  assume z_Hbp:"(~?z_hbo)"
  show FALSE
  proof (rule zenon_notand [OF z_Hbp])
   assume z_Hbq:"(~?z_hb)"
   show FALSE
   by (rule notE [OF z_Hbq z_Hb])
  next
   assume z_Hbr:"(~?z_hc)"
   show FALSE
   by (rule notE [OF z_Hbr z_Hc])
  qed
 next
  assume z_Hbl:"?z_hbl"
  show FALSE
  by (rule notE [OF z_He z_Hbl])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 50"; *} qed
lemma ob'205:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
assumes v'44: "(TypeOK)"
assumes v'45: "(a_VInv1a)"
assumes v'46: "(a_VInv2a)"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes w
assumes w_in : "(w \<in> (Value))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
assumes v'71: "((((arith_add ((b), ((Succ[0]))))) \<in> (Ballot)))"
assumes v'72: "(((greater (((arith_add ((b), ((Succ[0]))))), (a_ca)))) & ((SafeAt (((arith_add ((b), ((Succ[0]))))), (v)))) & ((ChosenIn ((a_ca), (w)))))"
assumes v'73: "((((arith_add ((b), ((Succ[0]))))) \<noteq> ((0))))"
assumes v'74: "((((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0])))))))) = (b)))"
assumes v'75: "(\<forall> b_1 \<in> (Ballot) : (\<forall> v_1 \<in> (Value) : ((((SafeAt ((b_1), (v_1)))) = ((((b_1) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply ((maxBal), (a))), (b_1))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (v_1)))) & (\<forall> a \<in> (Q_1) : (\<forall> w_1 \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w_1)))) \<Rightarrow> (((w_1) = (v_1)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((DidNotVoteIn ((a), (d)))))))))))))))"
shows "(\<exists> QQ \<in> (Quorum) : (\<exists> d \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : ((((((d) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((d), (v)))) & (\<forall> a \<in> (QQ) : (\<forall> x \<in> (Value) : ((((VotedFor ((a), (d), (x)))) \<Rightarrow> (((x) = (v)))))))))) & (\<forall> e \<in> ((isa_peri_peri_a (((arith_add ((d), ((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (QQ) : ((DidNotVoteIn ((a), (e)))))))))"(is "PROP ?ob'205")
proof -
ML_command {* writeln "*** TLAPS ENTER 205"; *}
show "PROP ?ob'205"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_007a3c.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_007a3c.znn.out
;; obligation #205
$hyp "v'44" TypeOK
$hyp "v'45" a_VInv1a
$hyp "v'46" a_VInv2a
$hyp "v_in" (TLA.in v Value)
$hyp "w_in" (TLA.in w Value)
$hyp "b_in" (TLA.in b Ballot)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "v'71" (TLA.in (arith.add b (TLA.fapply TLA.Succ 0))
Ballot)
$hyp "v'72" (/\ (arith.lt a_ca (arith.add b (TLA.fapply TLA.Succ 0)))
(SafeAt (arith.add b (TLA.fapply TLA.Succ 0)) v) (ChosenIn a_ca
w))
$hyp "v'73" (-. (= (arith.add b (TLA.fapply TLA.Succ 0))
0))
$hyp "v'74" (= (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))
b)
$hyp "v'75" (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v_1) (= (SafeAt b_1
v_1) (\/ (= b_1 0)
(TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le b_1
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 v_1)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w_1) (=> (VotedFor a a_ca_1 w_1) (= w_1
v_1)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q_1 ((a) (DidNotVoteIn a
d)))))))))))))))))
$goal (TLA.bEx Quorum ((QQ) (TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (/\ (=> (-. (= d
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt d v)
(TLA.bAll QQ ((a) (TLA.bAll Value ((x) (=> (VotedFor a d x) (= x v))))))))
(TLA.bAll (arith.intrange (arith.add d (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((e) (TLA.bAll QQ ((a) (DidNotVoteIn a
e))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"((a_ca < (b + 1))&(SafeAt((b + 1), v)&ChosenIn(a_ca, w)))" (is "?z_ho&?z_ht")
 using v'72 by blast
 have z_Hm:"bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v_1. (SafeAt(b_1, v_1)=((b_1=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b_1 <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b_1 +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v_1)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=v_1))))))))&bAll(isa'dotdot((a_ca_1 + 1), (b_1 +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))" (is "?z_hm")
 using v'75 by blast
 have z_Hi:"((b + 1) \\in Ballot)" (is "?z_hi")
 using v'71 by blast
 have z_Hk:"((b + 1)~=0)" (is "?z_hq~=_")
 using v'73 by blast
 have z_Hd:"(v \\in Value)" (is "?z_hd")
 using v_in by blast
 assume z_Hn:"(~bEx(Quorum, (\<lambda>QQ. bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(SafeAt(d, v)&bAll(QQ, (\<lambda>a. bAll(Value, (\<lambda>x. (VotedFor(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(QQ, (\<lambda>a. DidNotVoteIn(a, e)))))))))))" (is "~?z_hcw")
 have z_Ht: "?z_ht" (is "?z_hu&?z_hw")
 by (rule zenon_and_1 [OF z_Hj])
 have z_Hu: "?z_hu"
 by (rule zenon_and_0 [OF z_Ht])
 have z_Hdy_z_Hm: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v_1. (SafeAt(x, v_1)=((x=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v_1)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=v_1))))))))&bAll(isa'dotdot((a_ca_1 + 1), (x +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))) == ?z_hm" (is "?z_hdy == _")
 by (unfold bAll_def)
 have z_Hdy: "?z_hdy" (is "\\A x : ?z_heu(x)")
 by (unfold z_Hdy_z_Hm, fact z_Hm)
 have z_Hev_z_Hn: "(~(\\E x:((x \\in Quorum)&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(SafeAt(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (VotedFor(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. DidNotVoteIn(a, e))))))))))) == (~?z_hcw)" (is "?z_hev == ?z_hn")
 by (unfold bEx_def)
 have z_Hev: "?z_hev" (is "~(\\E x : ?z_hfi(x))")
 by (unfold z_Hev_z_Hn, fact z_Hn)
 have z_Hfj: "?z_heu(?z_hq)" (is "_=>?z_hfk")
 by (rule zenon_all_0 [of "?z_heu" "?z_hq", OF z_Hdy])
 show FALSE
 proof (rule zenon_imply [OF z_Hfj])
  assume z_Hfl:"(~?z_hi)"
  show FALSE
  by (rule notE [OF z_Hfl z_Hi])
 next
  assume z_Hfk:"?z_hfk"
  have z_Hfm_z_Hfk: "(\\A x:((x \\in Value)=>(SafeAt(?z_hq, x)=((?z_hq=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (?z_hq <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, x)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=x))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_hq +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))) == ?z_hfk" (is "?z_hfm == _")
  by (unfold bAll_def)
  have z_Hfm: "?z_hfm" (is "\\A x : ?z_hgn(x)")
  by (unfold z_Hfm_z_Hfk, fact z_Hfk)
  have z_Hgo: "?z_hgn(v)" (is "_=>?z_hgp")
  by (rule zenon_all_0 [of "?z_hgn" "v", OF z_Hfm])
  show FALSE
  proof (rule zenon_imply [OF z_Hgo])
   assume z_Hgq:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hgq z_Hd])
  next
   assume z_Hgp:"?z_hgp" (is "_=?z_hgr")
   have z_Hgs: "(TRUE=?z_hgr)" (is "?z_hgt=_")
   by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vdf. (zenon_Vdf=?z_hgr))" "?z_hu", OF z_Hgp z_Hu])
   have z_Hgr: "?z_hgr" (is "?z_hfs|?z_hgx")
   by (rule zenon_eq_true_x_0 [of "?z_hgr", OF z_Hgs])
   show FALSE
   proof (rule zenon_or [OF z_Hgr])
    assume z_Hfs:"?z_hfs"
    show FALSE
    by (rule notE [OF z_Hk z_Hfs])
   next
    assume z_Hgx:"?z_hgx"
    have z_Hgy_z_Hgx: "(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_hq <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(SafeAt(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (VotedFor(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. DidNotVoteIn(a, e))))))))))) == ?z_hgx" (is "?z_hgy == _")
    by (unfold bEx_def)
    have z_Hgy: "?z_hgy" (is "\\E x : ?z_hhc(x)")
    by (unfold z_Hgy_z_Hgx, fact z_Hgx)
    have z_Hhd: "?z_hhc((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_hq <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(SafeAt(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (VotedFor(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. DidNotVoteIn(a, e))))))))))))" (is "?z_hhf&?z_hhg")
    by (rule zenon_ex_choose_0 [of "?z_hhc", OF z_Hgy])
    have z_Hhf: "?z_hhf"
    by (rule zenon_and_0 [OF z_Hhd])
    have z_Hhg: "?z_hhg" (is "?z_hhh&?z_hhi")
    by (rule zenon_and_1 [OF z_Hhd])
    have z_Hhi: "?z_hhi"
    by (rule zenon_and_1 [OF z_Hhg])
    have z_Hhj: "~?z_hfi((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_hq <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(SafeAt(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (VotedFor(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. DidNotVoteIn(a, e))))))))))))"
    by (rule zenon_notex_0 [of "?z_hfi" "(CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_hq <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(SafeAt(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (VotedFor(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. DidNotVoteIn(a, e)))))))))))", OF z_Hev])
    show FALSE
    proof (rule zenon_notand [OF z_Hhj])
     assume z_Hhk:"(~?z_hhf)"
     show FALSE
     by (rule notE [OF z_Hhk z_Hhf])
    next
     assume z_Hhl:"(~?z_hhi)"
     show FALSE
     by (rule notE [OF z_Hhl z_Hhi])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 205"; *} qed
lemma ob'215:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
assumes v'44: "(TypeOK)"
assumes v'45: "(a_VInv1a)"
assumes v'46: "(a_VInv2a)"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes w
assumes w_in : "(w \<in> (Value))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes QQ
assumes QQ_in : "(QQ \<in> (Quorum))"
fixes d
assumes d_in : "(d \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))))"
fixes aa
assumes aa_in : "(aa \<in> (((QQ) \<inter> (Q))))"
assumes v'81: "((((~ ((leq ((a_ca), (d)))))) \<Longrightarrow> (FALSE)))"
shows "((leq ((a_ca), (d))))"(is "PROP ?ob'215")
proof -
ML_command {* writeln "*** TLAPS ENTER 215"; *}
show "PROP ?ob'215"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_5d2dea.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_5d2dea.znn.out
;; obligation #215
$hyp "v'44" TypeOK
$hyp "v'45" a_VInv1a
$hyp "v'46" a_VInv2a
$hyp "v_in" (TLA.in v Value)
$hyp "w_in" (TLA.in w Value)
$hyp "b_in" (TLA.in b Ballot)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "QQ_in" (TLA.in QQ Quorum)
$hyp "d_in" (TLA.in d (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))))
$hyp "aa_in" (TLA.in aa (TLA.cap QQ Q))
$hyp "v'81" (=> (-. (arith.le a_ca d)) F.)
$goal (arith.le a_ca
d)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hl:"((~(a_ca <= d))=>FALSE)" (is "?z_hm=>?z_hq")
 using v'81 by blast
 assume z_Hm:"?z_hm" (is "~?z_hn")
 show FALSE
 proof (rule zenon_imply [OF z_Hl])
  assume z_Hr:"(~?z_hm)"
  show FALSE
  by (rule notE [OF z_Hr z_Hm])
 next
  assume z_Hq:"?z_hq"
  show FALSE
  by (rule z_Hq)
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 215"; *} qed
lemma ob'178:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
assumes v'38: "(TypeOK)"
assumes v'45: "(fapply (([ b \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> ((isa_peri_peri_a (((0)), (b)))) : (\<forall> v \<in> (Value) : ((((SafeAt ((a_ca), (v)))) \<Rightarrow> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((a_ca), ((minus (((Succ[0]))))))))))) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((geq ((fapply ((maxBal), (a))), (a_ca_1)))) & (((DidNotVoteIn ((a), (a_ca_1)))) | ((VotedFor ((a), (a_ca_1), (v)))))))))))))]), ((0))))"
assumes v'46: "((\<And> b :: c. b \<in> (Nat) \<Longrightarrow> ((fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> ((isa_peri_peri_a (((0)), (b_1)))) : (\<forall> v \<in> (Value) : ((((SafeAt ((a_ca), (v)))) \<Rightarrow> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((a_ca), ((minus (((Succ[0]))))))))))) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((geq ((fapply ((maxBal), (a))), (a_ca_1)))) & (((DidNotVoteIn ((a), (a_ca_1)))) | ((VotedFor ((a), (a_ca_1), (v)))))))))))))]), (b))) \<Longrightarrow> (fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> ((isa_peri_peri_a (((0)), (b_1)))) : (\<forall> v \<in> (Value) : ((((SafeAt ((a_ca), (v)))) \<Rightarrow> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((a_ca), ((minus (((Succ[0]))))))))))) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((geq ((fapply ((maxBal), (a))), (a_ca_1)))) & (((DidNotVoteIn ((a), (a_ca_1)))) | ((VotedFor ((a), (a_ca_1), (v)))))))))))))]), ((arith_add ((b), ((Succ[0]))))))))))"
assumes v'47: "(\<forall>f : ((((fapply ((f), ((0)))) & (\<forall> n \<in> (Nat) : (((fapply ((f), (n))) \<Rightarrow> (fapply ((f), ((arith_add ((n), ((Succ[0]))))))))))) \<Rightarrow> (\<forall> n \<in> (Nat) : (fapply ((f), (n)))))))"
shows "(\<forall> b \<in> (Nat) : (fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> ((isa_peri_peri_a (((0)), (b_1)))) : (\<forall> v \<in> (Value) : ((((SafeAt ((a_ca), (v)))) \<Rightarrow> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((a_ca), ((minus (((Succ[0]))))))))))) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((geq ((fapply ((maxBal), (a))), (a_ca_1)))) & (((DidNotVoteIn ((a), (a_ca_1)))) | ((VotedFor ((a), (a_ca_1), (v)))))))))))))]), (b))))"(is "PROP ?ob'178")
proof -
ML_command {* writeln "*** TLAPS ENTER 178"; *}
show "PROP ?ob'178"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_6968f1.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_6968f1.znn.out
;; obligation #178
$hyp "v'38" TypeOK
$hyp "v'45" (TLA.fapply (TLA.Fcn arith.N ((b) (TLA.bAll (arith.intrange 0
b) ((a_ca) (TLA.bAll Value ((v) (=> (SafeAt a_ca v)
(TLA.bAll (arith.intrange 0 (arith.add a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (TLA.bEx Quorum ((Q) (TLA.bAll Q ((a) (/\ (arith.le a_ca_1
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_1) (VotedFor a a_ca_1
v)))))))))))))))) 0)
$hyp "v'46" (TLA.bAll arith.N ((b) (=> (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll (arith.intrange 0
b_1) ((a_ca) (TLA.bAll Value ((v) (=> (SafeAt a_ca v)
(TLA.bAll (arith.intrange 0 (arith.add a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (TLA.bEx Quorum ((Q) (TLA.bAll Q ((a) (/\ (arith.le a_ca_1
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_1) (VotedFor a a_ca_1
v)))))))))))))))) b) (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll (arith.intrange 0
b_1) ((a_ca) (TLA.bAll Value ((v) (=> (SafeAt a_ca v)
(TLA.bAll (arith.intrange 0 (arith.add a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (TLA.bEx Quorum ((Q) (TLA.bAll Q ((a) (/\ (arith.le a_ca_1
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_1) (VotedFor a a_ca_1
v)))))))))))))))) (arith.add b
(TLA.fapply TLA.Succ 0))))))
$hyp "v'47" (A. ((f) (=> (/\ (TLA.fapply f 0)
(TLA.bAll arith.N ((n) (=> (TLA.fapply f n) (TLA.fapply f (arith.add n
(TLA.fapply TLA.Succ 0)))))))
(TLA.bAll arith.N ((n) (TLA.fapply f n))))))
$goal (TLA.bAll arith.N ((b) (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll (arith.intrange 0
b_1) ((a_ca) (TLA.bAll Value ((v) (=> (SafeAt a_ca v)
(TLA.bAll (arith.intrange 0 (arith.add a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (TLA.bEx Quorum ((Q) (TLA.bAll Q ((a) (/\ (arith.le a_ca_1
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_1) (VotedFor a a_ca_1
v)))))))))))))))) b)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(\\A f:(((f[0])&bAll(Nat, (\<lambda>n. ((f[n])=>(f[(n + 1)])))))=>bAll(Nat, (\<lambda>n. (f[n])))))" (is "\\A x : ?z_hv(x)")
 using v'47 by blast
 have z_Hb:"(Fcn(Nat, (\<lambda>b. bAll(isa'dotdot(0, b), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))[0])" (is "?z_hb")
 using v'45 by blast
 have z_Hc:"bAll(Nat, (\<lambda>b. ((Fcn(Nat, (\<lambda>b. bAll(isa'dotdot(0, b), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))[b])=>(Fcn(Nat, (\<lambda>b. bAll(isa'dotdot(0, b), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))[(b + 1)]))))" (is "?z_hc")
 using v'46 by blast
 assume z_He:"(~bAll(Nat, (\<lambda>b. (Fcn(Nat, (\<lambda>b. bAll(isa'dotdot(0, b), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))[b]))))" (is "~?z_hci")
 have z_Hck: "?z_hv(Fcn(Nat, (\<lambda>b. bAll(isa'dotdot(0, b), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))))" (is "?z_hcl=>_")
 by (rule zenon_all_0 [of "?z_hv" "Fcn(Nat, (\<lambda>b. bAll(isa'dotdot(0, b), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))", OF z_Hd])
 show FALSE
 proof (rule zenon_imply [OF z_Hck])
  assume z_Hcm:"(~?z_hcl)"
  show FALSE
  proof (rule zenon_notand [OF z_Hcm])
   assume z_Hcn:"(~?z_hb)"
   show FALSE
   by (rule notE [OF z_Hcn z_Hb])
  next
   assume z_Hco:"(~?z_hc)"
   show FALSE
   by (rule notE [OF z_Hco z_Hc])
  qed
 next
  assume z_Hci:"?z_hci"
  show FALSE
  by (rule notE [OF z_He z_Hci])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 178"; *} qed
lemma ob'249:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
assumes v'43: "(TypeOK)"
assumes v'44: "(a_VInv1a)"
assumes v'45: "(a_VInv2a)"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes w
assumes w_in : "(w \<in> (Value))"
assumes v'54: "(fapply (([ b \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> (Nat) : ((((((((greater ((b), (a_ca)))) \<and> ((SafeAt ((b), (v)))))) \<and> ((ChosenIn ((a_ca), (w)))))) \<Rightarrow> (((v) = (w))))))]), ((0))))"
assumes v'55: "((\<And> b :: c. b \<in> (Nat) \<Longrightarrow> ((\<forall> i \<in> ((isa_peri_peri_a (((0)), (b)))) : (fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> (Nat) : ((((((((greater ((b_1), (a_ca)))) \<and> ((SafeAt ((b_1), (v)))))) \<and> ((ChosenIn ((a_ca), (w)))))) \<Rightarrow> (((v) = (w))))))]), (i)))) \<Longrightarrow> (fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> (Nat) : ((((((((greater ((b_1), (a_ca)))) \<and> ((SafeAt ((b_1), (v)))))) \<and> ((ChosenIn ((a_ca), (w)))))) \<Rightarrow> (((v) = (w))))))]), ((arith_add ((b), ((Succ[0]))))))))))"
assumes v'56: "(\<forall>f : ((((fapply ((f), ((0)))) & (\<forall> n \<in> (Nat) : (((\<forall> j \<in> ((isa_peri_peri_a (((0)), (n)))) : (fapply ((f), (j)))) \<Rightarrow> (fapply ((f), ((arith_add ((n), ((Succ[0]))))))))))) \<Rightarrow> (\<forall> n \<in> (Nat) : (fapply ((f), (n)))))))"
shows "(\<forall> b \<in> (Nat) : (fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> (Nat) : ((((((((greater ((b_1), (a_ca)))) \<and> ((SafeAt ((b_1), (v)))))) \<and> ((ChosenIn ((a_ca), (w)))))) \<Rightarrow> (((v) = (w))))))]), (b))))"(is "PROP ?ob'249")
proof -
ML_command {* writeln "*** TLAPS ENTER 249"; *}
show "PROP ?ob'249"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_5014ab.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_5014ab.znn.out
;; obligation #249
$hyp "v'43" TypeOK
$hyp "v'44" a_VInv1a
$hyp "v'45" a_VInv2a
$hyp "v_in" (TLA.in v Value)
$hyp "w_in" (TLA.in w Value)
$hyp "v'54" (TLA.fapply (TLA.Fcn arith.N ((b) (TLA.bAll arith.N ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b) (SafeAt b v)) (ChosenIn a_ca w)) (= v
w)))))) 0)
$hyp "v'55" (TLA.bAll arith.N ((b) (=> (TLA.bAll (arith.intrange 0
b) ((i) (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll arith.N ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b_1) (SafeAt b_1 v)) (ChosenIn a_ca w)) (= v
w)))))) i))) (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll arith.N ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b_1) (SafeAt b_1 v)) (ChosenIn a_ca w)) (= v w)))))) (arith.add b
(TLA.fapply TLA.Succ 0))))))
$hyp "v'56" (A. ((f) (=> (/\ (TLA.fapply f 0)
(TLA.bAll arith.N ((n) (=> (TLA.bAll (arith.intrange 0
n) ((j) (TLA.fapply f j))) (TLA.fapply f (arith.add n
(TLA.fapply TLA.Succ 0)))))))
(TLA.bAll arith.N ((n) (TLA.fapply f n))))))
$goal (TLA.bAll arith.N ((b) (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll arith.N ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b_1) (SafeAt b_1 v)) (ChosenIn a_ca w)) (= v
w)))))) b)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(\\A f:(((f[0])&bAll(Nat, (\<lambda>n. (bAll(isa'dotdot(0, n), (\<lambda>j. (f[j])))=>(f[(n + 1)])))))=>bAll(Nat, (\<lambda>j. (f[j])))))" (is "\\A x : ?z_hbc(x)")
 using v'56 by blast
 have z_Hf:"(Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&SafeAt(b, v))&ChosenIn(a_ca, w))=>(v=w))))))[0])" (is "?z_hf")
 using v'54 by blast
 have z_Hg:"bAll(Nat, (\<lambda>b. (bAll(isa'dotdot(0, b), (\<lambda>i. (Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&SafeAt(b, v))&ChosenIn(a_ca, w))=>(v=w))))))[i])))=>(Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&SafeAt(b, v))&ChosenIn(a_ca, w))=>(v=w))))))[(b + 1)]))))" (is "?z_hg")
 using v'55 by blast
 assume z_Hi:"(~bAll(Nat, (\<lambda>i. (Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&SafeAt(b, v))&ChosenIn(a_ca, w))=>(v=w))))))[i]))))" (is "~?z_hcb")
 have z_Hcc: "?z_hbc(Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&SafeAt(b, v))&ChosenIn(a_ca, w))=>(v=w)))))))" (is "?z_hcd=>_")
 by (rule zenon_all_0 [of "?z_hbc" "Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&SafeAt(b, v))&ChosenIn(a_ca, w))=>(v=w))))))", OF z_Hh])
 show FALSE
 proof (rule zenon_imply [OF z_Hcc])
  assume z_Hce:"(~?z_hcd)"
  show FALSE
  proof (rule zenon_notand [OF z_Hce])
   assume z_Hcf:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hcf z_Hf])
  next
   assume z_Hcg:"(~?z_hg)"
   show FALSE
   by (rule notE [OF z_Hcg z_Hg])
  qed
 next
  assume z_Hcb:"?z_hcb"
  show FALSE
  by (rule notE [OF z_Hi z_Hcb])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 249"; *} qed
lemma ob'137:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
assumes v'39: "(TypeOK)"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> ((isa_peri_peri_a (((0)), (b)))))"
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes cc
assumes cc_in : "(cc \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), (b)))))"
assumes v'71: "(fapply (([ b_1 \<in> (Ballot)  \<mapsto> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), (b_1)))) : (\<forall> v_1 \<in> (Value) : ((((SafeAt ((a_ca_1), (v_1)))) \<Rightarrow> (\<forall> a_ca_2 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((a_ca_1), ((minus (((Succ[0]))))))))))) : (\<exists> Q_1 \<in> (Quorum) : (\<forall> a \<in> (Q_1) : (((geq ((fapply ((maxBal), (a))), (a_ca_2)))) & (((DidNotVoteIn ((a), (a_ca_2)))) | ((VotedFor ((a), (a_ca_2), (v_1)))))))))))))]), (b)))"
assumes v'72: "((((cc) \<in> ((isa_peri_peri_a (((0)), (b)))))) & (((cc) \<noteq> ((minus (((Succ[0]))))))))"
shows "((((SafeAt ((cc), (v)))) \<Rightarrow> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((cc), ((minus (((Succ[0]))))))))))) : (\<exists> Q_1 \<in> (Quorum) : (\<forall> a \<in> (Q_1) : (((geq ((fapply ((maxBal), (a))), (a_ca_1)))) & (((DidNotVoteIn ((a), (a_ca_1)))) | ((VotedFor ((a), (a_ca_1), (v)))))))))))"(is "PROP ?ob'137")
proof -
ML_command {* writeln "*** TLAPS ENTER 137"; *}
show "PROP ?ob'137"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_ee3d17.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_ee3d17.znn.out
;; obligation #137
$hyp "v'39" TypeOK
$hyp "b_in" (TLA.in b Ballot)
$hyp "v_in" (TLA.in v Value)
$hyp "a_ca_in" (TLA.in a_ca (arith.intrange 0
b))
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "cc_in" (TLA.in cc (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
b))
$hyp "v'71" (TLA.fapply (TLA.Fcn Ballot ((b_1) (TLA.bAll (arith.intrange 0
b_1) ((a_ca_1) (TLA.bAll Value ((v_1) (=> (SafeAt a_ca_1 v_1)
(TLA.bAll (arith.intrange 0 (arith.add a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_2) (TLA.bEx Quorum ((Q_1) (TLA.bAll Q_1 ((a) (/\ (arith.le a_ca_2
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_2) (VotedFor a a_ca_2
v_1)))))))))))))))) b)
$hyp "v'72" (/\ (TLA.in cc (arith.intrange 0 b)) (-. (= cc
(arith.minus (TLA.fapply TLA.Succ 0)))))
$goal (=> (SafeAt cc v) (TLA.bAll (arith.intrange 0 (arith.add cc
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (TLA.bEx Quorum ((Q_1) (TLA.bAll Q_1 ((a) (/\ (arith.le a_ca_1
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_1) (VotedFor a a_ca_1
v))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"((cc \\in isa'dotdot(0, b))&(cc~= -.(1)))" (is "?z_hj&?z_ho")
 using v'72 by blast
 have z_Hg:"(Fcn(Ballot, (\<lambda>b_1. bAll(isa'dotdot(0, b_1), (\<lambda>a_ca_1. bAll(Value, (\<lambda>v_1. (SafeAt(a_ca_1, v_1)=>bAll(isa'dotdot(0, (a_ca_1 +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1))))))))))))))))[b])" (is "?z_hg")
 using v'71 by blast
 have z_Hc:"(v \\in Value)" (is "?z_hc")
 using v_in by blast
 have z_Hb:"(b \\in Ballot)" (is "?z_hb")
 using b_in by blast
 assume z_Hi:"(~(SafeAt(cc, v)=>bAll(isa'dotdot(0, (cc +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))" (is "~(?z_hca=>?z_hcb)")
 have z_Hj: "?z_hj"
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hca: "?z_hca"
 by (rule zenon_notimply_0 [OF z_Hi])
 have z_Hco: "(~?z_hcb)"
 by (rule zenon_notimply_1 [OF z_Hi])
 show FALSE
 proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vf. zenon_Vf)" "Ballot" "(\<lambda>b_1. bAll(isa'dotdot(0, b_1), (\<lambda>a_ca_1. bAll(Value, (\<lambda>v_1. (SafeAt(a_ca_1, v_1)=>bAll(isa'dotdot(0, (a_ca_1 +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1)))))))))))))))" "b", OF z_Hg])
  assume z_Hcr:"(~?z_hb)"
  show FALSE
  by (rule notE [OF z_Hcr z_Hb])
 next
  assume z_Hcs:"bAll(isa'dotdot(0, b), (\<lambda>a_ca_1. bAll(Value, (\<lambda>v_1. (SafeAt(a_ca_1, v_1)=>bAll(isa'dotdot(0, (a_ca_1 +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1))))))))))))))" (is "?z_hcs")
  have z_Hct_z_Hcs: "(\\A x:((x \\in isa'dotdot(0, b))=>bAll(Value, (\<lambda>v_1. (SafeAt(x, v_1)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1)))))))))))))) == ?z_hcs" (is "?z_hct == _")
  by (unfold bAll_def)
  have z_Hct: "?z_hct" (is "\\A x : ?z_hde(x)")
  by (unfold z_Hct_z_Hcs, fact z_Hcs)
  have z_Hdf: "?z_hde(cc)" (is "_=>?z_hdg")
  by (rule zenon_all_0 [of "?z_hde" "cc", OF z_Hct])
  show FALSE
  proof (rule zenon_imply [OF z_Hdf])
   assume z_Hdh:"(~?z_hj)"
   show FALSE
   by (rule notE [OF z_Hdh z_Hj])
  next
   assume z_Hdg:"?z_hdg"
   have z_Hdi_z_Hdg: "(\\A x:((x \\in Value)=>(SafeAt(cc, x)=>bAll(isa'dotdot(0, (cc +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, x)))))))))))) == ?z_hdg" (is "?z_hdi == _")
   by (unfold bAll_def)
   have z_Hdi: "?z_hdi" (is "\\A x : ?z_hdw(x)")
   by (unfold z_Hdi_z_Hdg, fact z_Hdg)
   have z_Hdx: "?z_hdw(v)" (is "_=>?z_hbz")
   by (rule zenon_all_0 [of "?z_hdw" "v", OF z_Hdi])
   show FALSE
   proof (rule zenon_imply [OF z_Hdx])
    assume z_Hdy:"(~?z_hc)"
    show FALSE
    by (rule notE [OF z_Hdy z_Hc])
   next
    assume z_Hbz:"?z_hbz"
    show FALSE
    proof (rule zenon_imply [OF z_Hbz])
     assume z_Hdz:"(~?z_hca)"
     show FALSE
     by (rule notE [OF z_Hdz z_Hca])
    next
     assume z_Hcb:"?z_hcb"
     show FALSE
     by (rule notE [OF z_Hco z_Hcb])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 137"; *} qed
lemma ob'54:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
assumes v'39: "(TypeOK)"
assumes v'46: "(\<forall> b \<in> (Ballot) : (fapply (([ b_1 \<in> (Ballot)  \<mapsto> (\<forall> a_ca \<in> ((isa_peri_peri_a (((0)), (b_1)))) : (\<forall> v \<in> (Value) : ((((SafeAt ((a_ca), (v)))) \<Rightarrow> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((a_ca), ((minus (((Succ[0]))))))))))) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((geq ((fapply ((maxBal), (a))), (a_ca_1)))) & (((DidNotVoteIn ((a), (a_ca_1)))) | ((VotedFor ((a), (a_ca_1), (v)))))))))))))]), (b))))"
assumes v'47: "(\<forall> b \<in> (Ballot) : (((b) \<in> ((isa_peri_peri_a (((0)), (b)))))))"
shows "(\<forall> b \<in> (Ballot) : (\<forall> v \<in> (Value) : ((((SafeAt ((b), (v)))) \<Rightarrow> (\<forall> a_ca \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((geq ((fapply ((maxBal), (a))), (a_ca)))) & (((DidNotVoteIn ((a), (a_ca)))) | ((VotedFor ((a), (a_ca), (v)))))))))))))"(is "PROP ?ob'54")
proof -
ML_command {* writeln "*** TLAPS ENTER 54"; *}
show "PROP ?ob'54"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_ea8232.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_ea8232.znn.out
;; obligation #54
$hyp "v'39" TypeOK
$hyp "v'46" (TLA.bAll Ballot ((b) (TLA.fapply (TLA.Fcn Ballot ((b_1) (TLA.bAll (arith.intrange 0
b_1) ((a_ca) (TLA.bAll Value ((v) (=> (SafeAt a_ca v)
(TLA.bAll (arith.intrange 0 (arith.add a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (TLA.bEx Quorum ((Q) (TLA.bAll Q ((a) (/\ (arith.le a_ca_1
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_1) (VotedFor a a_ca_1
v)))))))))))))))) b)))
$hyp "v'47" (TLA.bAll Ballot ((b) (TLA.in b (arith.intrange 0
b))))
$goal (TLA.bAll Ballot ((b) (TLA.bAll Value ((v) (=> (SafeAt b v)
(TLA.bAll (arith.intrange 0 (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (TLA.bEx Quorum ((Q) (TLA.bAll Q ((a) (/\ (arith.le a_ca
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca) (VotedFor a a_ca
v))))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"bAll(Ballot, (\<lambda>b. (Fcn(Ballot, (\<lambda>b_1. bAll(isa'dotdot(0, b_1), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))[b])))" (is "?z_hb")
 using v'46 by blast
 have z_Hc:"bAll(Ballot, (\<lambda>b. (b \\in isa'dotdot(0, b))))" (is "?z_hc")
 using v'47 by blast
 assume z_Hd:"(~bAll(Ballot, (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))" (is "~?z_hbu")
 have z_Hbv_z_Hb: "(\\A x:((x \\in Ballot)=>(Fcn(Ballot, (\<lambda>b_1. bAll(isa'dotdot(0, b_1), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))[x]))) == ?z_hb" (is "?z_hbv == _")
 by (unfold bAll_def)
 have z_Hbv: "?z_hbv" (is "\\A x : ?z_hca(x)")
 by (unfold z_Hbv_z_Hb, fact z_Hb)
 have z_Hcb_z_Hc: "(\\A x:((x \\in Ballot)=>(x \\in isa'dotdot(0, x)))) == ?z_hc" (is "?z_hcb == _")
 by (unfold bAll_def)
 have z_Hcb: "?z_hcb" (is "\\A x : ?z_hcf(x)")
 by (unfold z_Hcb_z_Hc, fact z_Hc)
 have z_Hcg_z_Hd: "(~(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))) == (~?z_hbu)" (is "?z_hcg == ?z_hd")
 by (unfold bAll_def)
 have z_Hcg: "?z_hcg" (is "~(\\A x : ?z_hcq(x))")
 by (unfold z_Hcg_z_Hd, fact z_Hd)
 have z_Hcr: "(\\E x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))" (is "\\E x : ?z_hct(x)")
 by (rule zenon_notallex_0 [of "?z_hcq", OF z_Hcg])
 have z_Hcu: "?z_hct((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))" (is "~(?z_hcw=>?z_hcx)")
 by (rule zenon_ex_choose_0 [of "?z_hct", OF z_Hcr])
 have z_Hcw: "?z_hcw"
 by (rule zenon_notimply_0 [OF z_Hcu])
 have z_Hcy: "(~?z_hcx)"
 by (rule zenon_notimply_1 [OF z_Hcu])
 have z_Hcz: "?z_hca((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))" (is "_=>?z_hda")
 by (rule zenon_all_0 [of "?z_hca" "(CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))", OF z_Hbv])
 show FALSE
 proof (rule zenon_imply [OF z_Hcz])
  assume z_Hdb:"(~?z_hcw)"
  show FALSE
  by (rule notE [OF z_Hdb z_Hcw])
 next
  assume z_Hda:"?z_hda"
  show FALSE
  proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vf. zenon_Vf)" "Ballot" "(\<lambda>b_1. bAll(isa'dotdot(0, b_1), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))" "(CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))", OF z_Hda])
   assume z_Hdb:"(~?z_hcw)"
   show FALSE
   by (rule notE [OF z_Hdb z_Hcw])
  next
   assume z_Hde:"bAll(isa'dotdot(0, (CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))), (\<lambda>a_ca. bAll(Value, (\<lambda>v. (SafeAt(a_ca, v)=>bAll(isa'dotdot(0, (a_ca +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))" (is "?z_hde")
   have z_Hdg_z_Hde: "(\\A x:((x \\in isa'dotdot(0, (CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))))=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))) == ?z_hde" (is "?z_hdg == _")
   by (unfold bAll_def)
   have z_Hdg: "?z_hdg" (is "\\A x : ?z_hdj(x)")
   by (unfold z_Hdg_z_Hde, fact z_Hde)
   have z_Hdk: "?z_hcf((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))" (is "_=>?z_hdl")
   by (rule zenon_all_0 [of "?z_hcf" "(CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))", OF z_Hcb])
   show FALSE
   proof (rule zenon_imply [OF z_Hdk])
    assume z_Hdb:"(~?z_hcw)"
    show FALSE
    by (rule notE [OF z_Hdb z_Hcw])
   next
    assume z_Hdl:"?z_hdl"
    have z_Hdm: "?z_hdj((CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v))))))))))))))))"
    by (rule zenon_all_0 [of "?z_hdj" "(CHOOSE x:(~((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_1. bEx(Quorum, (\<lambda>Q. bAll(Q, (\<lambda>a. ((a_ca_1 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_1)|VotedFor(a, a_ca_1, v)))))))))))))))", OF z_Hdg])
    show FALSE
    proof (rule zenon_imply [OF z_Hdm])
     assume z_Hdn:"(~?z_hdl)"
     show FALSE
     by (rule notE [OF z_Hdn z_Hdl])
    next
     assume z_Hcx:"?z_hcx"
     show FALSE
     by (rule notE [OF z_Hcy z_Hcx])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 54"; *} qed
lemma ob'302:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
assumes v'47: "((a_hef12f5554781c2213604492856f635a :: c))"
assumes v'48: "((a_hcce4fe22a2a1c0038d2e074f96de93a :: c))"
assumes v'49: "((a_h9c328584958d15e5963012a5e014e1a :: c))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes w
assumes w_in : "(w \<in> (Value))"
assumes v'57: "(((((0)) \<in> (Ballot))) & (\<forall> a_ca \<in> (Ballot) : ((~ ((greater (((0)), (a_ca))))))))"
shows "(fapply (([ b \<in> (Ballot)  \<mapsto> (\<forall> a_ca \<in> (Ballot) : ((((((((greater ((b), (a_ca)))) \<and> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b), (v)) :: c)))) \<and> ((hd7e54dd37577097417f9ca9a5c775e ((a_ca), (w)) :: c)))) \<Rightarrow> (((v) = (w))))))]), ((0))))"(is "PROP ?ob'302")
proof -
ML_command {* writeln "*** TLAPS ENTER 302"; *}
show "PROP ?ob'302"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_0f7259.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_0f7259.znn.out
;; obligation #302
$hyp "v'47" a_hef12f5554781c2213604492856f635a
$hyp "v'48" a_hcce4fe22a2a1c0038d2e074f96de93a
$hyp "v'49" a_h9c328584958d15e5963012a5e014e1a
$hyp "v_in" (TLA.in v Value)
$hyp "w_in" (TLA.in w Value)
$hyp "v'57" (/\ (TLA.in 0 Ballot) (TLA.bAll Ballot ((a_ca) (-. (arith.lt a_ca
0)))))
$goal (TLA.fapply (TLA.Fcn Ballot ((b) (TLA.bAll Ballot ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b) (a_hd4a7fa801d94bc2a9c69d39a405ea2a b v))
(hd7e54dd37577097417f9ca9a5c775e a_ca w)) (= v
w)))))) 0)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"((0 \\in Ballot)&bAll(Ballot, (\<lambda>a_ca. (~(a_ca < 0)))))" (is "?z_hh&?z_hk")
 using v'57 by blast
 assume z_Hg:"(~(Fcn(Ballot, (\<lambda>b. bAll(Ballot, (\<lambda>a_ca. ((((a_ca < b)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w))))))[0]))" (is "~?z_hp")
 have z_Hh: "?z_hh"
 by (rule zenon_and_0 [OF z_Hf])
 have z_Hk: "?z_hk"
 by (rule zenon_and_1 [OF z_Hf])
 have z_Hbe_z_Hk: "(\\A x:((x \\in Ballot)=>(~(x < 0)))) == ?z_hk" (is "?z_hbe == _")
 by (unfold bAll_def)
 have z_Hbe: "?z_hbe" (is "\\A x : ?z_hbk(x)")
 by (unfold z_Hbe_z_Hk, fact z_Hk)
 show FALSE
 proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vf. (~zenon_Vf))" "Ballot" "(\<lambda>b. bAll(Ballot, (\<lambda>a_ca. ((((a_ca < b)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w)))))" "0", OF z_Hg])
  assume z_Hbo:"(~?z_hh)"
  show FALSE
  by (rule notE [OF z_Hbo z_Hh])
 next
  assume z_Hbp:"(~bAll(Ballot, (\<lambda>a_ca. ((((a_ca < 0)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(0, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w)))))" (is "~?z_hbq")
  have z_Hbw_z_Hbp: "(~(\\A x:((x \\in Ballot)=>((((x < 0)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(0, v))&hd7e54dd37577097417f9ca9a5c775e(x, w))=>(v=w))))) == (~?z_hbq)" (is "?z_hbw == ?z_hbp")
  by (unfold bAll_def)
  have z_Hbw: "?z_hbw" (is "~(\\A x : ?z_hcd(x))")
  by (unfold z_Hbw_z_Hbp, fact z_Hbp)
  have z_Hce: "(\\E x:(~((x \\in Ballot)=>((((x < 0)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(0, v))&hd7e54dd37577097417f9ca9a5c775e(x, w))=>(v=w)))))" (is "\\E x : ?z_hcg(x)")
  by (rule zenon_notallex_0 [of "?z_hcd", OF z_Hbw])
  have z_Hch: "?z_hcg((CHOOSE x:(~((x \\in Ballot)=>((((x < 0)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(0, v))&hd7e54dd37577097417f9ca9a5c775e(x, w))=>(v=w))))))" (is "~(?z_hcj=>?z_hck)")
  by (rule zenon_ex_choose_0 [of "?z_hcg", OF z_Hce])
  have z_Hcj: "?z_hcj"
  by (rule zenon_notimply_0 [OF z_Hch])
  have z_Hcl: "(~?z_hck)" (is "~(?z_hcm=>?z_hbd)")
  by (rule zenon_notimply_1 [OF z_Hch])
  have z_Hcm: "?z_hcm" (is "?z_hcn&?z_hco")
  by (rule zenon_notimply_0 [OF z_Hcl])
  have z_Hcn: "?z_hcn" (is "?z_hcp&?z_hbv")
  by (rule zenon_and_0 [OF z_Hcm])
  have z_Hcp: "?z_hcp"
  by (rule zenon_and_0 [OF z_Hcn])
  have z_Hcq: "?z_hbk((CHOOSE x:(~((x \\in Ballot)=>((((x < 0)&?z_hbv)&hd7e54dd37577097417f9ca9a5c775e(x, w))=>?z_hbd)))))" (is "_=>?z_hcr")
  by (rule zenon_all_0 [of "?z_hbk" "(CHOOSE x:(~((x \\in Ballot)=>((((x < 0)&?z_hbv)&hd7e54dd37577097417f9ca9a5c775e(x, w))=>?z_hbd))))", OF z_Hbe])
  show FALSE
  proof (rule zenon_imply [OF z_Hcq])
   assume z_Hcs:"(~?z_hcj)"
   show FALSE
   by (rule notE [OF z_Hcs z_Hcj])
  next
   assume z_Hcr:"?z_hcr"
   show FALSE
   by (rule notE [OF z_Hcr z_Hcp])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 302"; *} qed
lemma ob'175:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
assumes v'39: "(TypeOK)"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> ((isa_peri_peri_a (((0)), (b)))))"
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes cc
assumes cc_in : "(cc \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), (b)))))"
assumes v'78: "((((cc) \<in> ((isa_peri_peri_a (((0)), (b)))))) & (((cc) \<noteq> ((minus (((Succ[0]))))))))"
assumes v'79: "(fapply (([ b_1 \<in> (Ballot)  \<mapsto> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), (b_1)))) : (\<forall> v_1 \<in> (Value) : ((((SafeAt ((a_ca_1), (v_1)))) \<Rightarrow> (\<forall> a_ca_2 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((a_ca_1), ((minus (((Succ[0]))))))))))) : (\<exists> Q_1 \<in> (Quorum) : (\<forall> a \<in> (Q_1) : (((geq ((fapply ((maxBal), (a))), (a_ca_2)))) & (((DidNotVoteIn ((a), (a_ca_2)))) | ((VotedFor ((a), (a_ca_2), (v_1)))))))))))))]), (b)))"
shows "(\<forall> v_1 \<in> (Value) : ((((SafeAt ((cc), (v_1)))) \<Rightarrow> (\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((cc), ((minus (((Succ[0]))))))))))) : (\<exists> Q_1 \<in> (Quorum) : (\<forall> a \<in> (Q_1) : (((geq ((fapply ((maxBal), (a))), (a_ca_1)))) & (((DidNotVoteIn ((a), (a_ca_1)))) | ((VotedFor ((a), (a_ca_1), (v_1))))))))))))"(is "PROP ?ob'175")
proof -
ML_command {* writeln "*** TLAPS ENTER 175"; *}
show "PROP ?ob'175"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_16790f.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_16790f.znn.out
;; obligation #175
$hyp "v'39" TypeOK
$hyp "b_in" (TLA.in b Ballot)
$hyp "v_in" (TLA.in v Value)
$hyp "a_ca_in" (TLA.in a_ca (arith.intrange 0
b))
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "cc_in" (TLA.in cc (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
b))
$hyp "v'78" (/\ (TLA.in cc (arith.intrange 0 b)) (-. (= cc
(arith.minus (TLA.fapply TLA.Succ 0)))))
$hyp "v'79" (TLA.fapply (TLA.Fcn Ballot ((b_1) (TLA.bAll (arith.intrange 0
b_1) ((a_ca_1) (TLA.bAll Value ((v_1) (=> (SafeAt a_ca_1 v_1)
(TLA.bAll (arith.intrange 0 (arith.add a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_2) (TLA.bEx Quorum ((Q_1) (TLA.bAll Q_1 ((a) (/\ (arith.le a_ca_2
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_2) (VotedFor a a_ca_2
v_1)))))))))))))))) b)
$goal (TLA.bAll Value ((v_1) (=> (SafeAt cc v_1) (TLA.bAll (arith.intrange 0
(arith.add cc
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (TLA.bEx Quorum ((Q_1) (TLA.bAll Q_1 ((a) (/\ (arith.le a_ca_1
(TLA.fapply maxBal a)) (\/ (DidNotVoteIn a a_ca_1) (VotedFor a a_ca_1
v_1))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"((cc \\in isa'dotdot(0, b))&(cc~= -.(1)))" (is "?z_hj&?z_ho")
 using v'78 by blast
 have z_Hb:"(b \\in Ballot)" (is "?z_hb")
 using b_in by blast
 have z_Hh:"(Fcn(Ballot, (\<lambda>b_1. bAll(isa'dotdot(0, b_1), (\<lambda>a_ca_1. bAll(Value, (\<lambda>v_1. (SafeAt(a_ca_1, v_1)=>bAll(isa'dotdot(0, (a_ca_1 +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1))))))))))))))))[b])" (is "?z_hh")
 using v'79 by blast
 assume z_Hi:"(~bAll(Value, (\<lambda>v_1. (SafeAt(cc, v_1)=>bAll(isa'dotdot(0, (cc +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1)))))))))))))" (is "~?z_hby")
 have z_Hj: "?z_hj"
 by (rule zenon_and_0 [OF z_Hg])
 show FALSE
 proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vf. zenon_Vf)" "Ballot" "(\<lambda>b_1. bAll(isa'dotdot(0, b_1), (\<lambda>a_ca_1. bAll(Value, (\<lambda>v_1. (SafeAt(a_ca_1, v_1)=>bAll(isa'dotdot(0, (a_ca_1 +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1)))))))))))))))" "b", OF z_Hh])
  assume z_Hch:"(~?z_hb)"
  show FALSE
  by (rule notE [OF z_Hch z_Hb])
 next
  assume z_Hci:"bAll(isa'dotdot(0, b), (\<lambda>a_ca_1. bAll(Value, (\<lambda>v_1. (SafeAt(a_ca_1, v_1)=>bAll(isa'dotdot(0, (a_ca_1 +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1))))))))))))))" (is "?z_hci")
  have z_Hcj_z_Hci: "(\\A x:((x \\in isa'dotdot(0, b))=>bAll(Value, (\<lambda>v_1. (SafeAt(x, v_1)=>bAll(isa'dotdot(0, (x +  -.(1))), (\<lambda>a_ca_2. bEx(Quorum, (\<lambda>Q_1. bAll(Q_1, (\<lambda>a. ((a_ca_2 <= (maxBal[a]))&(DidNotVoteIn(a, a_ca_2)|VotedFor(a, a_ca_2, v_1)))))))))))))) == ?z_hci" (is "?z_hcj == _")
  by (unfold bAll_def)
  have z_Hcj: "?z_hcj" (is "\\A x : ?z_hcu(x)")
  by (unfold z_Hcj_z_Hci, fact z_Hci)
  have z_Hcv: "?z_hcu(cc)"
  by (rule zenon_all_0 [of "?z_hcu" "cc", OF z_Hcj])
  show FALSE
  proof (rule zenon_imply [OF z_Hcv])
   assume z_Hcw:"(~?z_hj)"
   show FALSE
   by (rule notE [OF z_Hcw z_Hj])
  next
   assume z_Hby:"?z_hby"
   show FALSE
   by (rule notE [OF z_Hi z_Hby])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 175"; *} qed
lemma ob'321:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
assumes v'47: "((a_hef12f5554781c2213604492856f635a :: c))"
assumes v'48: "((a_hcce4fe22a2a1c0038d2e074f96de93a :: c))"
assumes v'49: "((a_h9c328584958d15e5963012a5e014e1a :: c))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes w
assumes w_in : "(w \<in> (Value))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
assumes v'74: "((((arith_add ((b), ((Succ[0]))))) \<in> (Ballot)))"
assumes v'75: "(((greater (((arith_add ((b), ((Succ[0]))))), (a_ca)))) & ((a_hd4a7fa801d94bc2a9c69d39a405ea2a (((arith_add ((b), ((Succ[0]))))), (v)) :: c)) & ((hd7e54dd37577097417f9ca9a5c775e ((a_ca), (w)) :: c)))"
assumes v'76: "((((arith_add ((b), ((Succ[0]))))) \<noteq> ((0))))"
assumes v'77: "((((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0])))))))) = (b)))"
assumes v'78: "(\<forall> b_1 \<in> (Ballot) : (\<forall> v_1 \<in> (Value) : ((((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b_1), (v_1)) :: c)) = ((((b_1) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (a))), (b_1))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((a_ca_1), (v_1)) :: c)) & (\<forall> a \<in> (Q_1) : (\<forall> w_1 \<in> (Value) : ((((a_hedffe1caafe019043ade750241d505a ((a), (a_ca_1), (w_1)) :: c)) \<Rightarrow> (((w_1) = (v_1)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((a_h16e0669e214bafdd37b2de01746035a ((a), (d)) :: c)))))))))))))"
shows "(\<exists> QQ \<in> (Quorum) : (\<exists> d \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : ((((((d) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((d), (v)) :: c)) & (\<forall> a \<in> (QQ) : (\<forall> x \<in> (Value) : ((((a_hedffe1caafe019043ade750241d505a ((a), (d), (x)) :: c)) \<Rightarrow> (((x) = (v)))))))))) & (\<forall> e \<in> ((isa_peri_peri_a (((arith_add ((d), ((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (QQ) : ((a_h16e0669e214bafdd37b2de01746035a ((a), (e)) :: c)))))))"(is "PROP ?ob'321")
proof -
ML_command {* writeln "*** TLAPS ENTER 321"; *}
show "PROP ?ob'321"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_a73912.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_a73912.znn.out
;; obligation #321
$hyp "v'47" a_hef12f5554781c2213604492856f635a
$hyp "v'48" a_hcce4fe22a2a1c0038d2e074f96de93a
$hyp "v'49" a_h9c328584958d15e5963012a5e014e1a
$hyp "v_in" (TLA.in v Value)
$hyp "w_in" (TLA.in w Value)
$hyp "b_in" (TLA.in b Ballot)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "v'74" (TLA.in (arith.add b (TLA.fapply TLA.Succ 0))
Ballot)
$hyp "v'75" (/\ (arith.lt a_ca (arith.add b (TLA.fapply TLA.Succ 0)))
(a_hd4a7fa801d94bc2a9c69d39a405ea2a (arith.add b (TLA.fapply TLA.Succ 0)) v)
(hd7e54dd37577097417f9ca9a5c775e a_ca w))
$hyp "v'76" (-. (= (arith.add b (TLA.fapply TLA.Succ 0))
0))
$hyp "v'77" (= (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))
b)
$hyp "v'78" (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v_1) (= (a_hd4a7fa801d94bc2a9c69d39a405ea2a b_1
v_1) (\/ (= b_1 0)
(TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le b_1
(TLA.fapply a_maxBalhash_primea a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a a_ca_1 v_1)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w_1) (=> (a_hedffe1caafe019043ade750241d505a a
a_ca_1 w_1) (= w_1 v_1)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q_1 ((a) (a_h16e0669e214bafdd37b2de01746035a a
d)))))))))))))))))
$goal (TLA.bEx Quorum ((QQ) (TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (/\ (=> (-. (= d
(arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a d v)
(TLA.bAll QQ ((a) (TLA.bAll Value ((x) (=> (a_hedffe1caafe019043ade750241d505a a
d x) (= x v)))))))) (TLA.bAll (arith.intrange (arith.add d
(TLA.fapply TLA.Succ 0)) (arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))) ((e) (TLA.bAll QQ ((a) (a_h16e0669e214bafdd37b2de01746035a a
e))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"((a_ca < (b + 1))&(a_hd4a7fa801d94bc2a9c69d39a405ea2a((b + 1), v)&hd7e54dd37577097417f9ca9a5c775e(a_ca, w)))" (is "?z_ho&?z_ht")
 using v'75 by blast
 have z_Hm:"bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v_1. (a_hd4a7fa801d94bc2a9c69d39a405ea2a(b_1, v_1)=((b_1=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b_1 <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (b_1 +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, v_1)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=v_1))))))))&bAll(isa'dotdot((a_ca_1 + 1), (b_1 +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d)))))))))))))))))" (is "?z_hm")
 using v'78 by blast
 have z_Hi:"((b + 1) \\in Ballot)" (is "?z_hi")
 using v'74 by blast
 have z_Hk:"((b + 1)~=0)" (is "?z_hq~=_")
 using v'76 by blast
 have z_Hd:"(v \\in Value)" (is "?z_hd")
 using v_in by blast
 assume z_Hn:"(~bEx(Quorum, (\<lambda>QQ. bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(d, v)&bAll(QQ, (\<lambda>a. bAll(Value, (\<lambda>x. (a_hedffe1caafe019043ade750241d505a(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(QQ, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, e)))))))))))" (is "~?z_hcw")
 have z_Ht: "?z_ht" (is "?z_hu&?z_hw")
 by (rule zenon_and_1 [OF z_Hj])
 have z_Hu: "?z_hu"
 by (rule zenon_and_0 [OF z_Ht])
 have z_Hdy_z_Hm: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v_1. (a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, v_1)=((x=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (x <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, v_1)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=v_1))))))))&bAll(isa'dotdot((a_ca_1 + 1), (x +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d))))))))))))))))) == ?z_hm" (is "?z_hdy == _")
 by (unfold bAll_def)
 have z_Hdy: "?z_hdy" (is "\\A x : ?z_heu(x)")
 by (unfold z_Hdy_z_Hm, fact z_Hm)
 have z_Hev_z_Hn: "(~(\\E x:((x \\in Quorum)&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (a_hedffe1caafe019043ade750241d505a(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, e))))))))))) == (~?z_hcw)" (is "?z_hev == ?z_hn")
 by (unfold bEx_def)
 have z_Hev: "?z_hev" (is "~(\\E x : ?z_hfi(x))")
 by (unfold z_Hev_z_Hn, fact z_Hn)
 have z_Hfj: "?z_heu(?z_hq)" (is "_=>?z_hfk")
 by (rule zenon_all_0 [of "?z_heu" "?z_hq", OF z_Hdy])
 show FALSE
 proof (rule zenon_imply [OF z_Hfj])
  assume z_Hfl:"(~?z_hi)"
  show FALSE
  by (rule notE [OF z_Hfl z_Hi])
 next
  assume z_Hfk:"?z_hfk"
  have z_Hfm_z_Hfk: "(\\A x:((x \\in Value)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(?z_hq, x)=((?z_hq=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (?z_hq <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, x)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=x))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_hq +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d))))))))))))))) == ?z_hfk" (is "?z_hfm == _")
  by (unfold bAll_def)
  have z_Hfm: "?z_hfm" (is "\\A x : ?z_hgn(x)")
  by (unfold z_Hfm_z_Hfk, fact z_Hfk)
  have z_Hgo: "?z_hgn(v)" (is "_=>?z_hgp")
  by (rule zenon_all_0 [of "?z_hgn" "v", OF z_Hfm])
  show FALSE
  proof (rule zenon_imply [OF z_Hgo])
   assume z_Hgq:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hgq z_Hd])
  next
   assume z_Hgp:"?z_hgp" (is "_=?z_hgr")
   have z_Hgs: "(TRUE=?z_hgr)" (is "?z_hgt=_")
   by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vdf. (zenon_Vdf=?z_hgr))" "?z_hu", OF z_Hgp z_Hu])
   have z_Hgr: "?z_hgr" (is "?z_hfs|?z_hgx")
   by (rule zenon_eq_true_x_0 [of "?z_hgr", OF z_Hgs])
   show FALSE
   proof (rule zenon_or [OF z_Hgr])
    assume z_Hfs:"?z_hfs"
    show FALSE
    by (rule notE [OF z_Hk z_Hfs])
   next
    assume z_Hgx:"?z_hgx"
    have z_Hgy_z_Hgx: "(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_hq <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (a_hedffe1caafe019043ade750241d505a(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, e))))))))))) == ?z_hgx" (is "?z_hgy == _")
    by (unfold bEx_def)
    have z_Hgy: "?z_hgy" (is "\\E x : ?z_hhc(x)")
    by (unfold z_Hgy_z_Hgx, fact z_Hgx)
    have z_Hhd: "?z_hhc((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_hq <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (a_hedffe1caafe019043ade750241d505a(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, e))))))))))))" (is "?z_hhf&?z_hhg")
    by (rule zenon_ex_choose_0 [of "?z_hhc", OF z_Hgy])
    have z_Hhf: "?z_hhf"
    by (rule zenon_and_0 [OF z_Hhd])
    have z_Hhg: "?z_hhg" (is "?z_hhh&?z_hhi")
    by (rule zenon_and_1 [OF z_Hhd])
    have z_Hhi: "?z_hhi"
    by (rule zenon_and_1 [OF z_Hhg])
    have z_Hhj: "~?z_hfi((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_hq <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (a_hedffe1caafe019043ade750241d505a(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, e))))))))))))"
    by (rule zenon_notex_0 [of "?z_hfi" "(CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_hq <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (?z_hq +  -.(1))), (\<lambda>d. (((d~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(d, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>x. (a_hedffe1caafe019043ade750241d505a(a, d, x)=>(x=v))))))))&bAll(isa'dotdot((d + 1), (?z_hq +  -.(1))), (\<lambda>e. bAll(x, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, e)))))))))))", OF z_Hev])
    show FALSE
    proof (rule zenon_notand [OF z_Hhj])
     assume z_Hhk:"(~?z_hhf)"
     show FALSE
     by (rule notE [OF z_Hhk z_Hhf])
    next
     assume z_Hhl:"(~?z_hhi)"
     show FALSE
     by (rule notE [OF z_Hhl z_Hhi])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 321"; *} qed
lemma ob'331:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
assumes v'47: "((a_hef12f5554781c2213604492856f635a :: c))"
assumes v'48: "((a_hcce4fe22a2a1c0038d2e074f96de93a :: c))"
assumes v'49: "((a_h9c328584958d15e5963012a5e014e1a :: c))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes w
assumes w_in : "(w \<in> (Value))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes QQ
assumes QQ_in : "(QQ \<in> (Quorum))"
fixes d
assumes d_in : "(d \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add (((arith_add ((b), ((Succ[0]))))), ((minus (((Succ[0]))))))))))))"
fixes aa
assumes aa_in : "(aa \<in> (((QQ) \<inter> (Q))))"
assumes v'84: "((((~ ((leq ((a_ca), (d)))))) \<Longrightarrow> (FALSE)))"
shows "((leq ((a_ca), (d))))"(is "PROP ?ob'331")
proof -
ML_command {* writeln "*** TLAPS ENTER 331"; *}
show "PROP ?ob'331"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_20746b.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_20746b.znn.out
;; obligation #331
$hyp "v'47" a_hef12f5554781c2213604492856f635a
$hyp "v'48" a_hcce4fe22a2a1c0038d2e074f96de93a
$hyp "v'49" a_h9c328584958d15e5963012a5e014e1a
$hyp "v_in" (TLA.in v Value)
$hyp "w_in" (TLA.in w Value)
$hyp "b_in" (TLA.in b Ballot)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "QQ_in" (TLA.in QQ Quorum)
$hyp "d_in" (TLA.in d (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add (arith.add b (TLA.fapply TLA.Succ 0))
(arith.minus (TLA.fapply TLA.Succ 0)))))
$hyp "aa_in" (TLA.in aa (TLA.cap QQ Q))
$hyp "v'84" (=> (-. (arith.le a_ca d)) F.)
$goal (arith.le a_ca
d)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hl:"((~(a_ca <= d))=>FALSE)" (is "?z_hm=>?z_hq")
 using v'84 by blast
 assume z_Hm:"?z_hm" (is "~?z_hn")
 show FALSE
 proof (rule zenon_imply [OF z_Hl])
  assume z_Hr:"(~?z_hm)"
  show FALSE
  by (rule notE [OF z_Hr z_Hm])
 next
  assume z_Hq:"?z_hq"
  show FALSE
  by (rule z_Hq)
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 331"; *} qed
lemma ob'365:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
assumes v'46: "((a_hef12f5554781c2213604492856f635a :: c))"
assumes v'47: "((a_hcce4fe22a2a1c0038d2e074f96de93a :: c))"
assumes v'48: "((a_h9c328584958d15e5963012a5e014e1a :: c))"
fixes v
assumes v_in : "(v \<in> (Value))"
fixes w
assumes w_in : "(w \<in> (Value))"
assumes v'57: "(fapply (([ b \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> (Nat) : ((((((((greater ((b), (a_ca)))) \<and> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b), (v)) :: c)))) \<and> ((hd7e54dd37577097417f9ca9a5c775e ((a_ca), (w)) :: c)))) \<Rightarrow> (((v) = (w))))))]), ((0))))"
assumes v'58: "((\<And> b :: c. b \<in> (Nat) \<Longrightarrow> ((\<forall> i \<in> ((isa_peri_peri_a (((0)), (b)))) : (fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> (Nat) : ((((((((greater ((b_1), (a_ca)))) \<and> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b_1), (v)) :: c)))) \<and> ((hd7e54dd37577097417f9ca9a5c775e ((a_ca), (w)) :: c)))) \<Rightarrow> (((v) = (w))))))]), (i)))) \<Longrightarrow> (fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> (Nat) : ((((((((greater ((b_1), (a_ca)))) \<and> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b_1), (v)) :: c)))) \<and> ((hd7e54dd37577097417f9ca9a5c775e ((a_ca), (w)) :: c)))) \<Rightarrow> (((v) = (w))))))]), ((arith_add ((b), ((Succ[0]))))))))))"
assumes v'59: "(\<forall>f : ((((fapply ((f), ((0)))) & (\<forall> n \<in> (Nat) : (((\<forall> j \<in> ((isa_peri_peri_a (((0)), (n)))) : (fapply ((f), (j)))) \<Rightarrow> (fapply ((f), ((arith_add ((n), ((Succ[0]))))))))))) \<Rightarrow> (\<forall> n \<in> (Nat) : (fapply ((f), (n)))))))"
shows "(\<forall> b \<in> (Nat) : (fapply (([ b_1 \<in> (Nat)  \<mapsto> (\<forall> a_ca \<in> (Nat) : ((((((((greater ((b_1), (a_ca)))) \<and> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b_1), (v)) :: c)))) \<and> ((hd7e54dd37577097417f9ca9a5c775e ((a_ca), (w)) :: c)))) \<Rightarrow> (((v) = (w))))))]), (b))))"(is "PROP ?ob'365")
proof -
ML_command {* writeln "*** TLAPS ENTER 365"; *}
show "PROP ?ob'365"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_287a99.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_287a99.znn.out
;; obligation #365
$hyp "v'46" a_hef12f5554781c2213604492856f635a
$hyp "v'47" a_hcce4fe22a2a1c0038d2e074f96de93a
$hyp "v'48" a_h9c328584958d15e5963012a5e014e1a
$hyp "v_in" (TLA.in v Value)
$hyp "w_in" (TLA.in w Value)
$hyp "v'57" (TLA.fapply (TLA.Fcn arith.N ((b) (TLA.bAll arith.N ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b) (a_hd4a7fa801d94bc2a9c69d39a405ea2a b v))
(hd7e54dd37577097417f9ca9a5c775e a_ca w)) (= v
w)))))) 0)
$hyp "v'58" (TLA.bAll arith.N ((b) (=> (TLA.bAll (arith.intrange 0
b) ((i) (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll arith.N ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b_1) (a_hd4a7fa801d94bc2a9c69d39a405ea2a b_1 v))
(hd7e54dd37577097417f9ca9a5c775e a_ca w)) (= v
w)))))) i))) (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll arith.N ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b_1) (a_hd4a7fa801d94bc2a9c69d39a405ea2a b_1 v))
(hd7e54dd37577097417f9ca9a5c775e a_ca w)) (= v w)))))) (arith.add b
(TLA.fapply TLA.Succ 0))))))
$hyp "v'59" (A. ((f) (=> (/\ (TLA.fapply f 0)
(TLA.bAll arith.N ((n) (=> (TLA.bAll (arith.intrange 0
n) ((j) (TLA.fapply f j))) (TLA.fapply f (arith.add n
(TLA.fapply TLA.Succ 0)))))))
(TLA.bAll arith.N ((n) (TLA.fapply f n))))))
$goal (TLA.bAll arith.N ((b) (TLA.fapply (TLA.Fcn arith.N ((b_1) (TLA.bAll arith.N ((a_ca) (=> (/\ (/\ (arith.lt a_ca
b_1) (a_hd4a7fa801d94bc2a9c69d39a405ea2a b_1 v))
(hd7e54dd37577097417f9ca9a5c775e a_ca w)) (= v
w)))))) b)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(\\A f:(((f[0])&bAll(Nat, (\<lambda>n. (bAll(isa'dotdot(0, n), (\<lambda>j. (f[j])))=>(f[(n + 1)])))))=>bAll(Nat, (\<lambda>j. (f[j])))))" (is "\\A x : ?z_hbc(x)")
 using v'59 by blast
 have z_Hf:"(Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w))))))[0])" (is "?z_hf")
 using v'57 by blast
 have z_Hg:"bAll(Nat, (\<lambda>b. (bAll(isa'dotdot(0, b), (\<lambda>i. (Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w))))))[i])))=>(Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w))))))[(b + 1)]))))" (is "?z_hg")
 using v'58 by blast
 assume z_Hi:"(~bAll(Nat, (\<lambda>i. (Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w))))))[i]))))" (is "~?z_hcb")
 have z_Hcc: "?z_hbc(Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w)))))))" (is "?z_hcd=>_")
 by (rule zenon_all_0 [of "?z_hbc" "Fcn(Nat, (\<lambda>b. bAll(Nat, (\<lambda>a_ca. ((((a_ca < b)&a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, v))&hd7e54dd37577097417f9ca9a5c775e(a_ca, w))=>(v=w))))))", OF z_Hh])
 show FALSE
 proof (rule zenon_imply [OF z_Hcc])
  assume z_Hce:"(~?z_hcd)"
  show FALSE
  proof (rule zenon_notand [OF z_Hce])
   assume z_Hcf:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hcf z_Hf])
  next
   assume z_Hcg:"(~?z_hg)"
   show FALSE
   by (rule notE [OF z_Hcg z_Hg])
  qed
 next
  assume z_Hcb:"?z_hcb"
  show FALSE
  by (rule notE [OF z_Hi z_Hcb])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 365"; *} qed
lemma ob'418:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'56: "(((TypeOK) \<Longrightarrow> (((Next) = (\<exists> self \<in> (Acceptor) : (\<exists> b \<in> (Ballot) : ((BallotAction ((self), (b))))))))))"
shows "(((TypeOK) \<Rightarrow> (((Next) = (\<exists> self \<in> (Acceptor) : (\<exists> b \<in> (Ballot) : ((BallotAction ((self), (b))))))))))"(is "PROP ?ob'418")
proof -
ML_command {* writeln "*** TLAPS ENTER 418"; *}
show "PROP ?ob'418"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_2cc0ca.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_2cc0ca.znn.out
;; obligation #418
$hyp "v'56" (=> TypeOK (= Next
(TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((b) (BallotAction self
b)))))))
$goal (=> TypeOK (= Next
(TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((b) (BallotAction self
b)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(TypeOK=>(Next=bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b. BallotAction(self, b)))))))" (is "_=>?z_hd")
 using v'56 by blast
 assume z_Hb:"(~(TypeOK=>?z_hd))"
 show FALSE
 by (rule notE [OF z_Hb z_Ha])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 418"; *} qed
lemma ob'438:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'56: "(((((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))) \<Longrightarrow> (\<And> self :: c. self \<in> (Acceptor) \<Longrightarrow> (\<And> b :: c. b \<in> (Ballot) \<Longrightarrow> (((BallotAction ((self), (b)))) \<Longrightarrow> ((((((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h9c328584958d15e5963012a5e014e1a :: c)))) \<and> ((a_hde69b2e11a77e40b5c91b849e88685a :: c)))) \<and> ((a_hfb87cccee30646b4043b294bd10930a :: c)))))))))"
assumes v'57: "(((((((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))) \<and> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))) \<Rightarrow> ((((((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h9c328584958d15e5963012a5e014e1a :: c)))) \<and> ((a_hde69b2e11a77e40b5c91b849e88685a :: c)))) \<and> ((a_hfb87cccee30646b4043b294bd10930a :: c))))))"
assumes v'58: "(((TypeOK) \<Rightarrow> (((Next) = (\<exists> self \<in> (Acceptor) : (\<exists> b \<in> (Ballot) : ((BallotAction ((self), (b))))))))))"
shows "(((((((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))))) \<Rightarrow> ((((((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h9c328584958d15e5963012a5e014e1a :: c)))) \<and> ((a_hde69b2e11a77e40b5c91b849e88685a :: c)))) \<and> ((a_hfb87cccee30646b4043b294bd10930a :: c))))))"(is "PROP ?ob'438")
proof -
ML_command {* writeln "*** TLAPS ENTER 438"; *}
show "PROP ?ob'438"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_c00141.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_c00141.znn.out
;; obligation #438
$hyp "v'56" (=> (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a)
a_VInv4a) (TLA.bAll Acceptor ((self) (TLA.bAll Ballot ((b) (=> (BallotAction self
b) (/\ (/\ (/\ a_hef12f5554781c2213604492856f635a
a_h9c328584958d15e5963012a5e014e1a) a_hde69b2e11a77e40b5c91b849e88685a)
a_hfb87cccee30646b4043b294bd10930a)))))))
$hyp "v'57" (=> (/\ (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a) a_VInv4a)
(= a_h4fd5f73954dc53af536c1c75068837a vars))
(/\ (/\ (/\ a_hef12f5554781c2213604492856f635a
a_h9c328584958d15e5963012a5e014e1a) a_hde69b2e11a77e40b5c91b849e88685a)
a_hfb87cccee30646b4043b294bd10930a))
$hyp "v'58" (=> TypeOK (= Next
(TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((b) (BallotAction self
b)))))))
$goal (=> (/\ (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a) a_VInv4a) (\/ Next
(= a_h4fd5f73954dc53af536c1c75068837a vars)))
(/\ (/\ (/\ a_hef12f5554781c2213604492856f635a
a_h9c328584958d15e5963012a5e014e1a) a_hde69b2e11a77e40b5c91b849e88685a)
a_hfb87cccee30646b4043b294bd10930a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"(((((TypeOK&a_VInv2a)&a_VInv3a)&a_VInv4a)&(a_h4fd5f73954dc53af536c1c75068837a=vars))=>(((a_hef12f5554781c2213604492856f635a&a_h9c328584958d15e5963012a5e014e1a)&a_hde69b2e11a77e40b5c91b849e88685a)&a_hfb87cccee30646b4043b294bd10930a))" (is "?z_he=>?z_hp")
 using v'57 by blast
 have z_Hc:"(TypeOK=>(Next=bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b. BallotAction(self, b)))))))" (is "_=>?z_hw")
 using v'58 by blast
 have z_Ha:"((((TypeOK&a_VInv2a)&a_VInv3a)&a_VInv4a)=>bAll(Acceptor, (\<lambda>self. bAll(Ballot, (\<lambda>b. (BallotAction(self, b)=>?z_hp))))))" (is "?z_hf=>?z_hbh")
 using v'56 by blast
 assume z_Hd:"(~((?z_hf&(Next|(a_h4fd5f73954dc53af536c1c75068837a=vars)))=>?z_hp))" (is "~(?z_hbn=>_)")
 have z_Hbn: "?z_hbn" (is "_&?z_hbo")
 by (rule zenon_notimply_0 [OF z_Hd])
 have z_Hbp: "(~?z_hp)" (is "~(?z_hq&_)")
 by (rule zenon_notimply_1 [OF z_Hd])
 have z_Hf: "?z_hf" (is "?z_hg&_")
 by (rule zenon_and_0 [OF z_Hbn])
 have z_Hbo: "?z_hbo" (is "_|?z_hm")
 by (rule zenon_and_1 [OF z_Hbn])
 have z_Hg: "?z_hg" (is "?z_hh&_")
 by (rule zenon_and_0 [OF z_Hf])
 have z_Hl: "a_VInv4a"
 by (rule zenon_and_1 [OF z_Hf])
 have z_Hh: "?z_hh"
 by (rule zenon_and_0 [OF z_Hg])
 have z_Hk: "a_VInv3a"
 by (rule zenon_and_1 [OF z_Hg])
 have z_Hi: "TypeOK"
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hj: "a_VInv2a"
 by (rule zenon_and_1 [OF z_Hh])
 show FALSE
 proof (rule zenon_or [OF z_Hbo])
  assume z_Hx:"Next"
  show FALSE
  proof (rule zenon_imply [OF z_Ha])
   assume z_Hbq:"(~?z_hf)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbq])
    assume z_Hbr:"(~?z_hg)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbr])
     assume z_Hbs:"(~?z_hh)"
     show FALSE
     proof (rule zenon_notand [OF z_Hbs])
      assume z_Hbt:"(~TypeOK)"
      show FALSE
      by (rule notE [OF z_Hbt z_Hi])
     next
      assume z_Hbu:"(~a_VInv2a)"
      show FALSE
      by (rule notE [OF z_Hbu z_Hj])
     qed
    next
     assume z_Hbv:"(~a_VInv3a)"
     show FALSE
     by (rule notE [OF z_Hbv z_Hk])
    qed
   next
    assume z_Hbw:"(~a_VInv4a)"
    show FALSE
    by (rule notE [OF z_Hbw z_Hl])
   qed
  next
   assume z_Hbh:"?z_hbh"
   have z_Hbx_z_Hbh: "(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>b. (BallotAction(x, b)=>?z_hp))))) == ?z_hbh" (is "?z_hbx == _")
   by (unfold bAll_def)
   have z_Hbx: "?z_hbx" (is "\\A x : ?z_hcf(x)")
   by (unfold z_Hbx_z_Hbh, fact z_Hbh)
   show FALSE
   proof (rule zenon_imply [OF z_Hc])
    assume z_Hbt:"(~TypeOK)"
    show FALSE
    by (rule notE [OF z_Hbt z_Hi])
   next
    assume z_Hw:"?z_hw" (is "_=?z_hy")
    have z_Hcg_z_Hw: "(Next=(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b)))))) == ?z_hw" (is "?z_hcg == _")
    by (unfold bEx_def)
    have z_Hcg: "?z_hcg" (is "_=?z_hch")
    by (unfold z_Hcg_z_Hw, fact z_Hw)
    have z_Hcl: "(TRUE=?z_hch)" (is "?z_hcm=_")
    by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vz. (zenon_Vz=?z_hch))" "Next", OF z_Hcg z_Hx])
    have z_Hch: "?z_hch" (is "\\E x : ?z_hcq(x)")
    by (rule zenon_eq_true_x_0 [of "?z_hch", OF z_Hcl])
    have z_Hcr: "?z_hcq((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))))" (is "?z_hct&?z_hcu")
    by (rule zenon_ex_choose_0 [of "?z_hcq", OF z_Hch])
    have z_Hct: "?z_hct"
    by (rule zenon_and_0 [OF z_Hcr])
    have z_Hcu: "?z_hcu"
    by (rule zenon_and_1 [OF z_Hcr])
    have z_Hcv_z_Hcu: "(\\E x:((x \\in Ballot)&BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x))) == ?z_hcu" (is "?z_hcv == _")
    by (unfold bEx_def)
    have z_Hcv: "?z_hcv" (is "\\E x : ?z_hcz(x)")
    by (unfold z_Hcv_z_Hcu, fact z_Hcu)
    have z_Hda: "?z_hcz((CHOOSE x:((x \\in Ballot)&BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x))))" (is "?z_hdc&?z_hdd")
    by (rule zenon_ex_choose_0 [of "?z_hcz", OF z_Hcv])
    have z_Hdc: "?z_hdc"
    by (rule zenon_and_0 [OF z_Hda])
    have z_Hdd: "?z_hdd"
    by (rule zenon_and_1 [OF z_Hda])
    have z_Hde: "?z_hcf((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))))" (is "_=>?z_hdf")
    by (rule zenon_all_0 [of "?z_hcf" "(CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b)))))", OF z_Hbx])
    show FALSE
    proof (rule zenon_imply [OF z_Hde])
     assume z_Hdg:"(~?z_hct)"
     show FALSE
     by (rule notE [OF z_Hdg z_Hct])
    next
     assume z_Hdf:"?z_hdf"
     have z_Hdh_z_Hdf: "(\\A x:((x \\in Ballot)=>(BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x)=>?z_hp))) == ?z_hdf" (is "?z_hdh == _")
     by (unfold bAll_def)
     have z_Hdh: "?z_hdh" (is "\\A x : ?z_hdk(x)")
     by (unfold z_Hdh_z_Hdf, fact z_Hdf)
     have z_Hdl: "?z_hdk((CHOOSE x:((x \\in Ballot)&BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x))))" (is "_=>?z_hdm")
     by (rule zenon_all_0 [of "?z_hdk" "(CHOOSE x:((x \\in Ballot)&BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x)))", OF z_Hdh])
     show FALSE
     proof (rule zenon_imply [OF z_Hdl])
      assume z_Hdn:"(~?z_hdc)"
      show FALSE
      by (rule notE [OF z_Hdn z_Hdc])
     next
      assume z_Hdm:"?z_hdm"
      show FALSE
      proof (rule zenon_imply [OF z_Hdm])
       assume z_Hdo:"(~?z_hdd)"
       show FALSE
       by (rule notE [OF z_Hdo z_Hdd])
      next
       assume z_Hp:"?z_hp"
       show FALSE
       by (rule notE [OF z_Hbp z_Hp])
      qed
     qed
    qed
   qed
  qed
 next
  assume z_Hm:"?z_hm"
  show FALSE
  proof (rule zenon_imply [OF z_Hb])
   assume z_Hdp:"(~?z_he)"
   show FALSE
   proof (rule zenon_notand [OF z_Hdp])
    assume z_Hbq:"(~?z_hf)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbq])
     assume z_Hbr:"(~?z_hg)"
     show FALSE
     proof (rule zenon_notand [OF z_Hbr])
      assume z_Hbs:"(~?z_hh)"
      show FALSE
      proof (rule zenon_notand [OF z_Hbs])
       assume z_Hbt:"(~TypeOK)"
       show FALSE
       by (rule notE [OF z_Hbt z_Hi])
      next
       assume z_Hbu:"(~a_VInv2a)"
       show FALSE
       by (rule notE [OF z_Hbu z_Hj])
      qed
     next
      assume z_Hbv:"(~a_VInv3a)"
      show FALSE
      by (rule notE [OF z_Hbv z_Hk])
     qed
    next
     assume z_Hbw:"(~a_VInv4a)"
     show FALSE
     by (rule notE [OF z_Hbw z_Hl])
    qed
   next
    assume z_Hdq:"(a_h4fd5f73954dc53af536c1c75068837a~=vars)"
    show FALSE
    by (rule notE [OF z_Hdq z_Hm])
   qed
  next
   assume z_Hp:"?z_hp"
   show FALSE
   by (rule notE [OF z_Hbp z_Hp])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 438"; *} qed
lemma ob'21:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
fixes v
assumes v_in : "(v \<in> (Value))"
(* usable definition Def suppressed *)
assumes v'40: "(\<forall> n \<in> (Nat) : (\<forall>g : (\<forall>h : (((\<forall> i \<in> ((isa_peri_peri_a (((0)), ((arith_add ((n), ((minus (((Succ[0]))))))))))) : (((fapply ((g), (i))) = (fapply ((h), (i)))))) \<Rightarrow> ((((Def ((g), (n)))) = ((Def ((h), (n)))))))))))"
assumes v'41: "((\<And> Def_1 :: c => c => c. ((\<forall> n \<in> (Nat) : (\<forall>g : (\<forall>h : (((\<forall> i \<in> ((isa_peri_peri_a (((0)), ((arith_add ((n), ((minus (((Succ[0]))))))))))) : (((fapply ((g), (i))) = (fapply ((h), (i)))))) \<Rightarrow> ((((Def_1 ((g), (n)))) = ((Def_1 ((h), (n))))))))))) \<Longrightarrow> (((Choice(%f. (((f) = ([ n \<in> (Nat)  \<mapsto> ((Def_1 ((f), (n))))]))))) = ([ n \<in> (Nat)  \<mapsto> ((Def_1 ((Choice(%f. (((f) = ([ n_1 \<in> (Nat)  \<mapsto> ((Def_1 ((f), (n_1))))]))))), (n))))]))))))"
shows "(((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((Def ((SA), (bb))))]))))) = ([ b \<in> (Nat)  \<mapsto> ((Def ((Choice(%SA. (((SA) = ([ bb \<in> (Nat)  \<mapsto> ((Def ((SA), (bb))))]))))), (b))))])))"(is "PROP ?ob'21")
proof -
ML_command {* writeln "*** TLAPS ENTER 21"; *}
show "PROP ?ob'21"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 21"; *} qed
lemma ob'516:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'57: "(VInv)"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'60: "((BallotAction ((self), (b))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes w
assumes w_in : "(w \<in> (Value))"
assumes v'75: "(\<forall> b_1 \<in> (Ballot) : (\<forall> v \<in> (Value) : ((((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b_1), (v)) :: c)) = ((((b_1) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (a))), (b_1))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((a_ca_1), (v)) :: c)) & (\<forall> a \<in> (Q) : (\<forall> w_1 \<in> (Value) : ((((a_hedffe1caafe019043ade750241d505a ((a), (a_ca_1), (w_1)) :: c)) \<Rightarrow> (((w_1) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((a_h16e0669e214bafdd37b2de01746035a ((a), (d)) :: c)))))))))))))"
assumes v'76: "((((((0)) \<in> (Ballot))) \<and> (\<forall> i \<in> ((isa_peri_peri_a (((0)), ((0))))) : (((i) = ((0)))))))"
shows "(fapply (([ i \<in> (Ballot)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (i)))) : ((((SafeAt ((j), (w)))) \<Rightarrow> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((j), (w)) :: c)))))]), ((0))))"(is "PROP ?ob'516")
proof -
ML_command {* writeln "*** TLAPS ENTER 516"; *}
show "PROP ?ob'516"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_fc1886.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_fc1886.znn.out
;; obligation #516
$hyp "v'57" VInv
$hyp "self_in" (TLA.in self Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'60" (BallotAction self
b)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "w_in" (TLA.in w Value)
$hyp "v'75" (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v) (= (a_hd4a7fa801d94bc2a9c69d39a405ea2a b_1
v) (\/ (= b_1 0) (TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le b_1
(TLA.fapply a_maxBalhash_primea a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a a_ca_1 v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w_1) (=> (a_hedffe1caafe019043ade750241d505a a
a_ca_1 w_1) (= w_1 v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (a_h16e0669e214bafdd37b2de01746035a a
d)))))))))))))))))
$hyp "v'76" (/\ (TLA.in 0 Ballot) (TLA.bAll (arith.intrange 0 0) ((i) (= i
0))))
$goal (TLA.fapply (TLA.Fcn Ballot ((i) (TLA.bAll (arith.intrange 0
i) ((j) (=> (SafeAt j w) (a_hd4a7fa801d94bc2a9c69d39a405ea2a j
w)))))) 0)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v. (a_hd4a7fa801d94bc2a9c69d39a405ea2a(b_1, v)=((b_1=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (b_1 <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (b_1 +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), (b_1 +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d)))))))))))))))))" (is "?z_hg")
 using v'75 by blast
 have z_Hf:"(w \\in Value)" (is "?z_hf")
 using w_in by blast
 have z_Hh:"((0 \\in Ballot)&bAll(isa'dotdot(0, 0), (\<lambda>i. (i=0))))" (is "?z_hcj&?z_hck")
 using v'76 by blast
 assume z_Hi:"(~(Fcn(Ballot, (\<lambda>i. bAll(isa'dotdot(0, i), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w))))))[0]))" (is "~?z_hcp")
 have z_Hcz_z_Hg: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v. (a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), (x +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d))))))))))))))))) == ?z_hg" (is "?z_hcz == _")
 by (unfold bAll_def)
 have z_Hcz: "?z_hcz" (is "\\A x : ?z_hdw(x)")
 by (unfold z_Hcz_z_Hg, fact z_Hg)
 have z_Hcj: "?z_hcj"
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hck: "?z_hck"
 by (rule zenon_and_1 [OF z_Hh])
 have z_Hdx_z_Hck: "(\\A x:((x \\in isa'dotdot(0, 0))=>(x=0))) == ?z_hck" (is "?z_hdx == _")
 by (unfold bAll_def)
 have z_Hdx: "?z_hdx" (is "\\A x : ?z_hea(x)")
 by (unfold z_Hdx_z_Hck, fact z_Hck)
 show FALSE
 proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vf. (~zenon_Vf))" "Ballot" "(\<lambda>i. bAll(isa'dotdot(0, i), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w)))))" "0", OF z_Hi])
  assume z_Hee:"(~?z_hcj)"
  show FALSE
  by (rule notE [OF z_Hee z_Hcj])
 next
  assume z_Hef:"(~bAll(isa'dotdot(0, 0), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w)))))" (is "~?z_heg")
  have z_Heh_z_Hef: "(~(\\A x:((x \\in isa'dotdot(0, 0))=>(SafeAt(x, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, w))))) == (~?z_heg)" (is "?z_heh == ?z_hef")
  by (unfold bAll_def)
  have z_Heh: "?z_heh" (is "~(\\A x : ?z_hen(x))")
  by (unfold z_Heh_z_Hef, fact z_Hef)
  have z_Heo: "(\\E x:(~((x \\in isa'dotdot(0, 0))=>(SafeAt(x, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, w)))))" (is "\\E x : ?z_heq(x)")
  by (rule zenon_notallex_0 [of "?z_hen", OF z_Heh])
  have z_Her: "?z_heq((CHOOSE x:(~((x \\in isa'dotdot(0, 0))=>(SafeAt(x, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, w))))))" (is "~(?z_het=>?z_heu)")
  by (rule zenon_ex_choose_0 [of "?z_heq", OF z_Heo])
  have z_Het: "?z_het"
  by (rule zenon_notimply_0 [OF z_Her])
  have z_Hev: "(~?z_heu)" (is "~(?z_hew=>?z_hex)")
  by (rule zenon_notimply_1 [OF z_Her])
  have z_Hey: "(~?z_hex)"
  by (rule zenon_notimply_1 [OF z_Hev])
  have z_Hez: "?z_hea((CHOOSE x:(~((x \\in isa'dotdot(0, 0))=>(SafeAt(x, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, w))))))" (is "_=>?z_hfa")
  by (rule zenon_all_0 [of "?z_hea" "(CHOOSE x:(~((x \\in isa'dotdot(0, 0))=>(SafeAt(x, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, w)))))", OF z_Hdx])
  show FALSE
  proof (rule zenon_imply [OF z_Hez])
   assume z_Hfb:"(~?z_het)"
   show FALSE
   by (rule notE [OF z_Hfb z_Het])
  next
   assume z_Hfa:"?z_hfa" (is "?z_hes=_")
   have z_Hfc: "?z_hdw(0)" (is "_=>?z_hfd")
   by (rule zenon_all_0 [of "?z_hdw" "0", OF z_Hcz])
   show FALSE
   proof (rule zenon_imply [OF z_Hfc])
    assume z_Hee:"(~?z_hcj)"
    show FALSE
    by (rule notE [OF z_Hee z_Hcj])
   next
    assume z_Hfd:"?z_hfd"
    have z_Hfe_z_Hfd: "(\\A x:((x \\in Value)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(0, x)=((0=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (0 <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (0 +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=x))))))))&bAll(isa'dotdot((a_ca_1 + 1), (0 +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d))))))))))))))) == ?z_hfd" (is "?z_hfe == _")
    by (unfold bAll_def)
    have z_Hfe: "?z_hfe" (is "\\A x : ?z_hgh(x)")
    by (unfold z_Hfe_z_Hfd, fact z_Hfd)
    have z_Hgi: "?z_hgh(w)" (is "_=>?z_hgj")
    by (rule zenon_all_0 [of "?z_hgh" "w", OF z_Hfe])
    show FALSE
    proof (rule zenon_imply [OF z_Hgi])
     assume z_Hgk:"(~?z_hf)"
     show FALSE
     by (rule notE [OF z_Hgk z_Hf])
    next
     assume z_Hgj:"?z_hgj" (is "?z_hgl=?z_hgm")
     show FALSE
     proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vge. (?z_hgl=zenon_Vge))" "(0=0)" "bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (0 <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (0 +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, w)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (0 +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d)))))))))))", OF z_Hgj])
      assume z_Hhf:"(?z_hgm=TRUE)" (is "_=?z_hhg")
      assume z_Hhh:"(?z_hgl=?z_hhg)"
      have z_Hgm: "?z_hgm" (is "?z_hfk|?z_hgq")
      by (rule zenon_eq_x_true_0 [of "?z_hgm", OF z_Hhf])
      show FALSE
      proof (rule zenon_np_eq_l [of "?z_hex" "?z_hgl" "?z_hgm", OF z_Hey z_Hgj])
       assume z_Hhi:"(?z_hex~=?z_hgl)"
       show FALSE
       proof (rule zenon_noteq [of "?z_hgl"])
        have z_Hhj: "(?z_hgl~=?z_hgl)"
        by (rule subst [where P="(\<lambda>zenon_Vrf. (a_hd4a7fa801d94bc2a9c69d39a405ea2a(zenon_Vrf, w)~=?z_hgl))", OF z_Hfa], fact z_Hhi)
        thus "(?z_hgl~=?z_hgl)" .
       qed
      next
       assume z_Hho:"(~?z_hgm)"
       show FALSE
       by (rule notE [OF z_Hho z_Hgm])
      qed
     next
      assume z_Hhp:"(?z_hgm=FALSE)" (is "_=?z_hhq")
      assume z_Hhr:"(?z_hgl=?z_hhq)"
      have z_Hho: "(~?z_hgm)" (is "~(?z_hfk|?z_hgq)")
      by (rule zenon_eq_x_false_0 [of "?z_hgm", OF z_Hhp])
      have z_Hhs: "(0~=0)"
      by (rule zenon_notor_0 [OF z_Hho])
      show FALSE
      by (rule zenon_noteq [OF z_Hhs])
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 516"; *} qed
lemma ob'535:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'57: "(VInv)"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'60: "((BallotAction ((self), (b))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes w
assumes w_in : "(w \<in> (Value))"
fixes d
assumes d_in : "(d \<in> (Ballot))"
fixes e
assumes e_in : "(e \<in> ((isa_peri_peri_a (((0)), ((arith_add ((d), ((Succ[0])))))))))"
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
assumes v'97: "(\<forall> aa \<in> (Q) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (aa))), (e)))))"
assumes v'98: "(\<exists> cc \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((e), ((minus (((Succ[0]))))))))))) : ((((((cc) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((cc), (w)) :: c)) & (\<forall> ax \<in> (Q) : (\<forall> z \<in> (Value) : ((((a_hedffe1caafe019043ade750241d505a ((ax), (cc), (z)) :: c)) \<Rightarrow> (((z) = (w)))))))))) & (\<forall> dd \<in> ((isa_peri_peri_a (((arith_add ((cc), ((Succ[0]))))), ((arith_add ((e), ((minus (((Succ[0]))))))))))) : (\<forall> ax \<in> (Q) : ((a_h16e0669e214bafdd37b2de01746035a ((ax), (dd)) :: c))))))"
assumes v'99: "((((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((e), (w)) :: c)) = ((((e) = ((0)))) | (\<exists> a_Qunde_1a \<in> (Quorum) : ((\<forall> aa \<in> (a_Qunde_1a) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (aa))), (e))))) & (\<exists> a_cunde_1a \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((e), ((minus (((Succ[0]))))))))))) : ((((((a_cunde_1a) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((a_cunde_1a), (w)) :: c)) & (\<forall> aa \<in> (a_Qunde_1a) : (\<forall> a_wunde_1a \<in> (Value) : ((((a_hedffe1caafe019043ade750241d505a ((aa), (a_cunde_1a), (a_wunde_1a)) :: c)) \<Rightarrow> (((a_wunde_1a) = (w)))))))))) & (\<forall> a_dunde_1a \<in> ((isa_peri_peri_a (((arith_add ((a_cunde_1a), ((Succ[0]))))), ((arith_add ((e), ((minus (((Succ[0]))))))))))) : (\<forall> aa \<in> (a_Qunde_1a) : ((a_h16e0669e214bafdd37b2de01746035a ((aa), (a_dunde_1a)) :: c)))))))))))"
shows "((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((e), (w)) :: c))"(is "PROP ?ob'535")
proof -
ML_command {* writeln "*** TLAPS ENTER 535"; *}
show "PROP ?ob'535"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_b76d8c.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_b76d8c.znn.out
;; obligation #535
$hyp "v'57" VInv
$hyp "self_in" (TLA.in self Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'60" (BallotAction self
b)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "w_in" (TLA.in w Value)
$hyp "d_in" (TLA.in d Ballot)
$hyp "e_in" (TLA.in e (arith.intrange 0 (arith.add d
(TLA.fapply TLA.Succ 0))))
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "v'97" (TLA.bAll Q ((aa) (arith.le e
(TLA.fapply a_maxBalhash_primea aa))))
$hyp "v'98" (TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add e (arith.minus (TLA.fapply TLA.Succ 0)))) ((cc) (/\ (=> (-. (= cc
(arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a cc w)
(TLA.bAll Q ((ax) (TLA.bAll Value ((z) (=> (a_hedffe1caafe019043ade750241d505a ax
cc z) (= z w)))))))) (TLA.bAll (arith.intrange (arith.add cc
(TLA.fapply TLA.Succ 0)) (arith.add e
(arith.minus (TLA.fapply TLA.Succ 0)))) ((dd) (TLA.bAll Q ((ax) (a_h16e0669e214bafdd37b2de01746035a ax
dd))))))))
$hyp "v'99" (= (a_hd4a7fa801d94bc2a9c69d39a405ea2a e w) (\/ (= e 0)
(TLA.bEx Quorum ((a_Qunde_1a) (/\ (TLA.bAll a_Qunde_1a ((aa) (arith.le e
(TLA.fapply a_maxBalhash_primea aa))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add e
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_cunde_1a) (/\ (=> (-. (= a_cunde_1a
(arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a a_cunde_1a w)
(TLA.bAll a_Qunde_1a ((aa) (TLA.bAll Value ((a_wunde_1a) (=> (a_hedffe1caafe019043ade750241d505a aa
a_cunde_1a a_wunde_1a) (= a_wunde_1a w))))))))
(TLA.bAll (arith.intrange (arith.add a_cunde_1a (TLA.fapply TLA.Succ 0))
(arith.add e
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_dunde_1a) (TLA.bAll a_Qunde_1a ((aa) (a_h16e0669e214bafdd37b2de01746035a aa
a_dunde_1a)))))))))))))
$goal (a_hd4a7fa801d94bc2a9c69d39a405ea2a e
w)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hl:"(a_hd4a7fa801d94bc2a9c69d39a405ea2a(e, w)=((e=0)|bEx(Quorum, (\<lambda>a_Qunde_1a. (bAll(a_Qunde_1a, (\<lambda>aa. (e <= (a_maxBalhash_primea[aa]))))&bEx(isa'dotdot( -.(1), (e +  -.(1))), (\<lambda>a_cunde_1a. (((a_cunde_1a~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_cunde_1a, w)&bAll(a_Qunde_1a, (\<lambda>aa. bAll(Value, (\<lambda>a_wunde_1a. (a_hedffe1caafe019043ade750241d505a(aa, a_cunde_1a, a_wunde_1a)=>(a_wunde_1a=w))))))))&bAll(isa'dotdot((a_cunde_1a + 1), (e +  -.(1))), (\<lambda>a_dunde_1a. bAll(a_Qunde_1a, (\<lambda>aa. a_h16e0669e214bafdd37b2de01746035a(aa, a_dunde_1a)))))))))))))" (is "?z_hn=?z_hq")
 using v'99 by blast
 have z_Hi:"(Q \\in Quorum)" (is "?z_hi")
 using Q_in by blast
 have z_Hj:"bAll(Q, (\<lambda>aa. (e <= (a_maxBalhash_primea[aa]))))" (is "?z_hj")
 using v'97 by blast
 have z_Hk:"bEx(isa'dotdot( -.(1), (e +  -.(1))), (\<lambda>cc. (((cc~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(cc, w)&bAll(Q, (\<lambda>ax. bAll(Value, (\<lambda>z. (a_hedffe1caafe019043ade750241d505a(ax, cc, z)=>(z=w))))))))&bAll(isa'dotdot((cc + 1), (e +  -.(1))), (\<lambda>dd. bAll(Q, (\<lambda>ax. a_h16e0669e214bafdd37b2de01746035a(ax, dd))))))))" (is "?z_hk")
 using v'98 by blast
 assume z_Hm:"(~?z_hn)"
 show FALSE
 proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vg. (?z_hn=zenon_Vg))" "(e=0)" "bEx(Quorum, (\<lambda>a_Qunde_1a. (bAll(a_Qunde_1a, (\<lambda>aa. (e <= (a_maxBalhash_primea[aa]))))&bEx(isa'dotdot( -.(1), (e +  -.(1))), (\<lambda>a_cunde_1a. (((a_cunde_1a~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_cunde_1a, w)&bAll(a_Qunde_1a, (\<lambda>aa. bAll(Value, (\<lambda>a_wunde_1a. (a_hedffe1caafe019043ade750241d505a(aa, a_cunde_1a, a_wunde_1a)=>(a_wunde_1a=w))))))))&bAll(isa'dotdot((a_cunde_1a + 1), (e +  -.(1))), (\<lambda>a_dunde_1a. bAll(a_Qunde_1a, (\<lambda>aa. a_h16e0669e214bafdd37b2de01746035a(aa, a_dunde_1a)))))))))))", OF z_Hl])
  assume z_Hdj:"(?z_hq=TRUE)" (is "_=?z_hdk")
  assume z_Hdl:"(?z_hn=?z_hdk)"
  have z_Hn: "?z_hn"
  by (rule zenon_eq_x_true_0 [of "?z_hn", OF z_Hdl])
  show FALSE
  by (rule notE [OF z_Hm z_Hn])
 next
  assume z_Hdm:"(?z_hq=FALSE)" (is "_=?z_hdn")
  assume z_Hdo:"(?z_hn=?z_hdn)"
  have z_Hdp: "(~?z_hq)" (is "~(?z_hr|?z_ht)")
  by (rule zenon_eq_x_false_0 [of "?z_hq", OF z_Hdm])
  have z_Hdq: "(~?z_ht)"
  by (rule zenon_notor_1 [OF z_Hdp])
  have z_Hdr_z_Hdq: "(~(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>aa. (e <= (a_maxBalhash_primea[aa]))))&bEx(isa'dotdot( -.(1), (e +  -.(1))), (\<lambda>a_cunde_1a. (((a_cunde_1a~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_cunde_1a, w)&bAll(x, (\<lambda>aa. bAll(Value, (\<lambda>a_wunde_1a. (a_hedffe1caafe019043ade750241d505a(aa, a_cunde_1a, a_wunde_1a)=>(a_wunde_1a=w))))))))&bAll(isa'dotdot((a_cunde_1a + 1), (e +  -.(1))), (\<lambda>a_dunde_1a. bAll(x, (\<lambda>aa. a_h16e0669e214bafdd37b2de01746035a(aa, a_dunde_1a)))))))))))) == (~?z_ht)" (is "?z_hdr == ?z_hdq")
  by (unfold bEx_def)
  have z_Hdr: "?z_hdr" (is "~(\\E x : ?z_heh(x))")
  by (unfold z_Hdr_z_Hdq, fact z_Hdq)
  have z_Hei: "~?z_heh(Q)" (is "~(_&?z_hej)")
  by (rule zenon_notex_0 [of "?z_heh" "Q", OF z_Hdr])
  show FALSE
  proof (rule zenon_notand [OF z_Hei])
   assume z_Hek:"(~?z_hi)"
   show FALSE
   by (rule notE [OF z_Hek z_Hi])
  next
   assume z_Hel:"(~?z_hej)"
   show FALSE
   proof (rule zenon_notand [OF z_Hel])
    assume z_Hem:"(~?z_hj)"
    show FALSE
    by (rule notE [OF z_Hem z_Hj])
   next
    assume z_Hen:"(~?z_hk)"
    show FALSE
    by (rule notE [OF z_Hen z_Hk])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 535"; *} qed
lemma ob'539:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'57: "(VInv)"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'60: "((BallotAction ((self), (b))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes w
assumes w_in : "(w \<in> (Value))"
fixes d
assumes d_in : "(d \<in> (Ballot))"
fixes e
assumes e_in : "(e \<in> ((isa_peri_peri_a (((0)), ((arith_add ((d), ((Succ[0])))))))))"
assumes v'89: "((((((arith_add ((d), ((Succ[0]))))) \<in> (Ballot))) \<and> ((((arith_add ((d), ((Succ[0]))))) \<noteq> ((0))))))"
assumes v'90: "((SafeAt ((e), (w))))"
assumes v'91: "(((e) = ((arith_add ((d), ((Succ[0])))))))"
assumes v'92: "(\<forall> b_1 \<in> (Ballot) : (\<forall> v \<in> (Value) : ((((SafeAt ((b_1), (v)))) = ((((b_1) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (b_1))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w_1 \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w_1)))) \<Rightarrow> (((w_1) = (v)))))))))) & (\<forall> d_1 \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d_1)))))))))))))))"
shows "(\<exists> Q \<in> (Quorum) : ((\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (e))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((e), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca_1), (w)))) & (\<forall> a \<in> (Q) : (\<forall> w_1 \<in> (Value) : ((((VotedFor ((a), (a_ca_1), (w_1)))) \<Rightarrow> (((w_1) = (w)))))))))) & (\<forall> d_1 \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((e), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d_1))))))))))"(is "PROP ?ob'539")
proof -
ML_command {* writeln "*** TLAPS ENTER 539"; *}
show "PROP ?ob'539"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_8b6d17.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_8b6d17.znn.out
;; obligation #539
$hyp "v'57" VInv
$hyp "self_in" (TLA.in self Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'60" (BallotAction self
b)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "w_in" (TLA.in w Value)
$hyp "d_in" (TLA.in d Ballot)
$hyp "e_in" (TLA.in e (arith.intrange 0 (arith.add d
(TLA.fapply TLA.Succ 0))))
$hyp "v'89" (/\ (TLA.in (arith.add d (TLA.fapply TLA.Succ 0)) Ballot)
(-. (= (arith.add d (TLA.fapply TLA.Succ 0)) 0)))
$hyp "v'90" (SafeAt e w)
$hyp "v'91" (= e (arith.add d
(TLA.fapply TLA.Succ 0)))
$hyp "v'92" (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v) (= (SafeAt b_1 v)
(\/ (= b_1 0) (TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le b_1
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w_1) (=> (VotedFor a a_ca_1 w_1) (= w_1
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d_1) (TLA.bAll Q ((a) (DidNotVoteIn a
d_1)))))))))))))))))
$goal (TLA.bEx Quorum ((Q) (/\ (TLA.bAll Q ((a) (arith.le e
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add e
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca_1 w)
(TLA.bAll Q ((a) (TLA.bAll Value ((w_1) (=> (VotedFor a a_ca_1 w_1) (= w_1
w)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add e
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d_1) (TLA.bAll Q ((a) (DidNotVoteIn a
d_1)))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hk:"(e=(d + 1))" (is "_=?z_ho")
 using v'91 by blast
 have z_Hi:"((?z_ho \\in Ballot)&(?z_ho~=0))" (is "?z_hr&?z_ht")
 using v'89 by blast
 have z_Hf:"(w \\in Value)" (is "?z_hf")
 using w_in by blast
 have z_Hj:"SafeAt(e, w)" (is "?z_hj")
 using v'90 by blast
 have z_Hl:"bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v. (SafeAt(b_1, v)=((b_1=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (b_1 <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b_1 +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), (b_1 +  -.(1))), (\<lambda>d_1. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d_1)))))))))))))))))" (is "?z_hl")
 using v'92 by blast
 assume z_Hm:"(~bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (e <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (e +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (e +  -.(1))), (\<lambda>d_1. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))" (is "~?z_hcs")
 have z_Hr: "?z_hr"
 by (rule zenon_and_0 [OF z_Hi])
 have z_Ht: "?z_ht"
 by (rule zenon_and_1 [OF z_Hi])
 have z_Hdo_z_Hl: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), (x +  -.(1))), (\<lambda>d_1. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))))))) == ?z_hl" (is "?z_hdo == _")
 by (unfold bAll_def)
 have z_Hdo: "?z_hdo" (is "\\A x : ?z_hel(x)")
 by (unfold z_Hdo_z_Hl, fact z_Hl)
 have z_Hem_z_Hm: "(~(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (e <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (e +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (e +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1)))))))))))) == (~?z_hcs)" (is "?z_hem == ?z_hm")
 by (unfold bEx_def)
 have z_Hem: "?z_hem" (is "~(\\E x : ?z_hfb(x))")
 by (unfold z_Hem_z_Hm, fact z_Hm)
 have z_Hfc: "SafeAt(?z_ho, w)" (is "?z_hfc")
 by (rule subst [where P="(\<lambda>zenon_Vlca. SafeAt(zenon_Vlca, w))", OF z_Hk z_Hj])
 have z_Hfg: "?z_hel(?z_ho)" (is "_=>?z_hfh")
 by (rule zenon_all_0 [of "?z_hel" "?z_ho", OF z_Hdo])
 show FALSE
 proof (rule zenon_imply [OF z_Hfg])
  assume z_Hfi:"(~?z_hr)"
  show FALSE
  by (rule notE [OF z_Hfi z_Hr])
 next
  assume z_Hfh:"?z_hfh"
  have z_Hfj_z_Hfh: "(\\A x:((x \\in Value)=>(SafeAt(?z_ho, x)=((?z_ho=0)|bEx(Quorum, (\<lambda>Q. (bAll(Q, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, x)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=x))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))))) == ?z_hfh" (is "?z_hfj == _")
  by (unfold bAll_def)
  have z_Hfj: "?z_hfj" (is "\\A x : ?z_hgm(x)")
  by (unfold z_Hfj_z_Hfh, fact z_Hfh)
  have z_Hgn: "?z_hgm(w)" (is "_=>?z_hgo")
  by (rule zenon_all_0 [of "?z_hgm" "w", OF z_Hfj])
  show FALSE
  proof (rule zenon_imply [OF z_Hgn])
   assume z_Hgp:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hgp z_Hf])
  next
   assume z_Hgo:"?z_hgo" (is "_=?z_hgq")
   have z_Hgr: "(TRUE=?z_hgq)" (is "?z_hgs=_")
   by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vxg. (zenon_Vxg=?z_hgq))" "?z_hfc", OF z_Hgo z_Hfc])
   have z_Hgq: "?z_hgq" (is "?z_hfp|?z_hgw")
   by (rule zenon_eq_true_x_0 [of "?z_hgq", OF z_Hgr])
   show FALSE
   proof (rule zenon_or [OF z_Hgq])
    assume z_Hfp:"?z_hfp"
    show FALSE
    by (rule notE [OF z_Ht z_Hfp])
   next
    assume z_Hgw:"?z_hgw"
    have z_Hgx_z_Hgw: "(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))) == ?z_hgw" (is "?z_hgx == _")
    by (unfold bEx_def)
    have z_Hgx: "?z_hgx" (is "\\E x : ?z_hhf(x)")
    by (unfold z_Hgx_z_Hgw, fact z_Hgw)
    have z_Hhg: "?z_hhf((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))" (is "?z_hhi&?z_hhj")
    by (rule zenon_ex_choose_0 [of "?z_hhf", OF z_Hgx])
    have z_Hhi: "?z_hhi"
    by (rule zenon_and_0 [OF z_Hhg])
    have z_Hhj: "?z_hhj" (is "?z_hhk&?z_hhl")
    by (rule zenon_and_1 [OF z_Hhg])
    have z_Hhk: "?z_hhk"
    by (rule zenon_and_0 [OF z_Hhj])
    have z_Hhl: "?z_hhl"
    by (rule zenon_and_1 [OF z_Hhj])
    have z_Hhm_z_Hhk: "(\\A x:((x \\in (CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))=>(?z_ho <= (maxBal[x])))) == ?z_hhk" (is "?z_hhm == _")
    by (unfold bAll_def)
    have z_Hhm: "?z_hhm" (is "\\A x : ?z_hhr(x)")
    by (unfold z_Hhm_z_Hhk, fact z_Hhk)
    have z_Hhs_z_Hhl: "(\\E x:((x \\in isa'dotdot( -.(1), (?z_ho +  -.(1))))&(((x~= -.(1))=>(SafeAt(x, w)&bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, x, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((x + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1)))))))) == ?z_hhl" (is "?z_hhs == _")
    by (unfold bEx_def)
    have z_Hhs: "?z_hhs" (is "\\E x : ?z_hil(x)")
    by (unfold z_Hhs_z_Hhl, fact z_Hhl)
    have z_Him: "?z_hil((CHOOSE x:((x \\in isa'dotdot( -.(1), (?z_ho +  -.(1))))&(((x~= -.(1))=>(SafeAt(x, w)&bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, x, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((x + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1)))))))))" (is "?z_hio&?z_hip")
    by (rule zenon_ex_choose_0 [of "?z_hil", OF z_Hhs])
    have z_Hio: "?z_hio"
    by (rule zenon_and_0 [OF z_Him])
    have z_Hip: "?z_hip" (is "?z_hiq&?z_hir")
    by (rule zenon_and_1 [OF z_Him])
    have z_Hiq: "?z_hiq" (is "?z_his=>?z_hit")
    by (rule zenon_and_0 [OF z_Hip])
    have z_Hir: "?z_hir"
    by (rule zenon_and_1 [OF z_Hip])
    have z_Hiu: "~?z_hfb((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))" (is "~(_&?z_hiv)")
    by (rule zenon_notex_0 [of "?z_hfb" "(CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1)))))))))))", OF z_Hem])
    show FALSE
    proof (rule zenon_notand [OF z_Hiu])
     assume z_Hiw:"(~?z_hhi)"
     show FALSE
     by (rule notE [OF z_Hiw z_Hhi])
    next
     assume z_Hix:"(~?z_hiv)" (is "~(?z_hiy&?z_hiz)")
     show FALSE
     proof (rule zenon_notand [OF z_Hix])
      assume z_Hja:"(~?z_hiy)"
      have z_Hjb_z_Hja: "(~(\\A x:((x \\in (CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))=>(e <= (maxBal[x]))))) == (~?z_hiy)" (is "?z_hjb == ?z_hja")
      by (unfold bAll_def)
      have z_Hjb: "?z_hjb" (is "~(\\A x : ?z_hjf(x))")
      by (unfold z_Hjb_z_Hja, fact z_Hja)
      have z_Hjg: "(\\E x:(~((x \\in (CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))=>(e <= (maxBal[x])))))" (is "\\E x : ?z_hji(x)")
      by (rule zenon_notallex_0 [of "?z_hjf", OF z_Hjb])
      have z_Hjj: "?z_hji((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))=>(e <= (maxBal[x]))))))" (is "~(?z_hjl=>?z_hjm)")
      by (rule zenon_ex_choose_0 [of "?z_hji", OF z_Hjg])
      have z_Hjl: "?z_hjl"
      by (rule zenon_notimply_0 [OF z_Hjj])
      have z_Hjn: "(~?z_hjm)"
      by (rule zenon_notimply_1 [OF z_Hjj])
      have z_Hjo: "(~(?z_ho <= (maxBal[(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))=>(e <= (maxBal[x])))))])))" (is "~?z_hjp")
      by (rule subst [where P="(\<lambda>zenon_Vdca. (~(zenon_Vdca <= (maxBal[(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))=>(e <= (maxBal[x])))))]))))", OF z_Hk z_Hjn])
      have z_Hjv: "?z_hhr((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))=>(e <= (maxBal[x]))))))"
      by (rule zenon_all_0 [of "?z_hhr" "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))))=>(e <= (maxBal[x])))))", OF z_Hhm])
      show FALSE
      proof (rule zenon_imply [OF z_Hjv])
       assume z_Hjw:"(~?z_hjl)"
       show FALSE
       by (rule notE [OF z_Hjw z_Hjl])
      next
       assume z_Hjp:"?z_hjp"
       show FALSE
       by (rule notE [OF z_Hjo z_Hjp])
      qed
     next
      assume z_Hjx:"(~?z_hiz)"
      have z_Hjy: "(~bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (e +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1)))))))))" (is "~?z_hjz")
      by (rule subst [where P="(\<lambda>zenon_Vpca. (~bEx(isa'dotdot( -.(1), (zenon_Vpca +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (e +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1))))))))))", OF z_Hk z_Hjx])
      have z_Hkm_z_Hjy: "(~(\\E x:((x \\in isa'dotdot( -.(1), (?z_ho +  -.(1))))&(((x~= -.(1))=>(SafeAt(x, w)&bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, x, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((x + 1), (e +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1))))))))) == (~?z_hjz)" (is "?z_hkm == ?z_hjy")
      by (unfold bEx_def)
      have z_Hkm: "?z_hkm" (is "~(\\E x : ?z_hks(x))")
      by (unfold z_Hkm_z_Hjy, fact z_Hjy)
      have z_Hkt: "~?z_hks((CHOOSE x:((x \\in isa'dotdot( -.(1), (?z_ho +  -.(1))))&(((x~= -.(1))=>(SafeAt(x, w)&bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, x, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((x + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1)))))))))" (is "~(_&?z_hku)")
      by (rule zenon_notex_0 [of "?z_hks" "(CHOOSE x:((x \\in isa'dotdot( -.(1), (?z_ho +  -.(1))))&(((x~= -.(1))=>(SafeAt(x, w)&bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, x, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((x + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1))))))))", OF z_Hkm])
      show FALSE
      proof (rule zenon_notand [OF z_Hkt])
       assume z_Hkv:"(~?z_hio)"
       show FALSE
       by (rule notE [OF z_Hkv z_Hio])
      next
       assume z_Hkw:"(~?z_hku)" (is "~(_&?z_hkx)")
       show FALSE
       proof (rule zenon_notand [OF z_Hkw])
        assume z_Hky:"(~?z_hiq)"
        show FALSE
        by (rule notE [OF z_Hky z_Hiq])
       next
        assume z_Hkz:"(~?z_hkx)"
        have z_Hla: "(~?z_hir)"
        by (rule subst [where P="(\<lambda>zenon_Vkba. (~bAll(isa'dotdot(((CHOOSE x:((x \\in isa'dotdot( -.(1), (?z_ho +  -.(1))))&(((x~= -.(1))=>(SafeAt(x, w)&bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, x, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((x + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1)))))))) + 1), (zenon_Vkba +  -.(1))), (\<lambda>d_1. bAll((CHOOSE x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (?z_ho <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (?z_ho +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(SafeAt(a_ca_1, w)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w_1. (VotedFor(a, a_ca_1, w_1)=>(w_1=w))))))))&bAll(isa'dotdot((a_ca_1 + 1), (?z_ho +  -.(1))), (\<lambda>d_1. bAll(x, (\<lambda>a. DidNotVoteIn(a, d_1))))))))))), (\<lambda>a. DidNotVoteIn(a, d_1)))))))", OF z_Hk z_Hkz])
        show FALSE
        by (rule notE [OF z_Hla z_Hir])
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 539"; *} qed
lemma ob'628:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'57: "(VInv)"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'60: "((BallotAction ((self), (b))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes w
assumes w_in : "(w \<in> (Value))"
fixes d
assumes d_in : "(d \<in> (Ballot))"
fixes e
assumes e_in : "(e \<in> ((isa_peri_peri_a (((0)), ((arith_add ((d), ((Succ[0])))))))))"
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
assumes v'98: "(\<forall> b_1 \<in> (Ballot) : (\<forall> v \<in> (Value) : ((((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b_1), (v)) :: c)) = ((((b_1) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (a))), (b_1))))) & (\<exists> a_ca_1 \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : ((((((a_ca_1) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((a_ca_1), (v)) :: c)) & (\<forall> a \<in> (Q_1) : (\<forall> w_1 \<in> (Value) : ((((a_hedffe1caafe019043ade750241d505a ((a), (a_ca_1), (w_1)) :: c)) \<Rightarrow> (((w_1) = (v)))))))))) & (\<forall> d_1 \<in> ((isa_peri_peri_a (((arith_add ((a_ca_1), ((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((a_h16e0669e214bafdd37b2de01746035a ((a), (d_1)) :: c)))))))))))))"
assumes v'99: "(((e) \<in> (Ballot)))"
shows "((((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((e), (w)) :: c)) = ((((e) = ((0)))) | (\<exists> a_Qunde_1a \<in> (Quorum) : ((\<forall> aa \<in> (a_Qunde_1a) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (aa))), (e))))) & (\<exists> a_cunde_1a \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((e), ((minus (((Succ[0]))))))))))) : ((((((a_cunde_1a) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((a_cunde_1a), (w)) :: c)) & (\<forall> aa \<in> (a_Qunde_1a) : (\<forall> a_wunde_1a \<in> (Value) : ((((a_hedffe1caafe019043ade750241d505a ((aa), (a_cunde_1a), (a_wunde_1a)) :: c)) \<Rightarrow> (((a_wunde_1a) = (w)))))))))) & (\<forall> a_dunde_1a \<in> ((isa_peri_peri_a (((arith_add ((a_cunde_1a), ((Succ[0]))))), ((arith_add ((e), ((minus (((Succ[0]))))))))))) : (\<forall> aa \<in> (a_Qunde_1a) : ((a_h16e0669e214bafdd37b2de01746035a ((aa), (a_dunde_1a)) :: c)))))))))))"(is "PROP ?ob'628")
proof -
ML_command {* writeln "*** TLAPS ENTER 628"; *}
show "PROP ?ob'628"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_4c12c5.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_4c12c5.znn.out
;; obligation #628
$hyp "v'57" VInv
$hyp "self_in" (TLA.in self Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'60" (BallotAction self
b)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "w_in" (TLA.in w Value)
$hyp "d_in" (TLA.in d Ballot)
$hyp "e_in" (TLA.in e (arith.intrange 0 (arith.add d
(TLA.fapply TLA.Succ 0))))
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "v'98" (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v) (= (a_hd4a7fa801d94bc2a9c69d39a405ea2a b_1
v) (\/ (= b_1 0) (TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le b_1
(TLA.fapply a_maxBalhash_primea a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (/\ (=> (-. (= a_ca_1
(arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a a_ca_1 v)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w_1) (=> (a_hedffe1caafe019043ade750241d505a a
a_ca_1 w_1) (= w_1 v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca_1
(TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d_1) (TLA.bAll Q_1 ((a) (a_h16e0669e214bafdd37b2de01746035a a
d_1)))))))))))))))))
$hyp "v'99" (TLA.in e Ballot)
$goal (= (a_hd4a7fa801d94bc2a9c69d39a405ea2a e w) (\/ (= e 0)
(TLA.bEx Quorum ((a_Qunde_1a) (/\ (TLA.bAll a_Qunde_1a ((aa) (arith.le e
(TLA.fapply a_maxBalhash_primea aa))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add e
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_cunde_1a) (/\ (=> (-. (= a_cunde_1a
(arith.minus (TLA.fapply TLA.Succ 0))))
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a a_cunde_1a w)
(TLA.bAll a_Qunde_1a ((aa) (TLA.bAll Value ((a_wunde_1a) (=> (a_hedffe1caafe019043ade750241d505a aa
a_cunde_1a a_wunde_1a) (= a_wunde_1a w))))))))
(TLA.bAll (arith.intrange (arith.add a_cunde_1a (TLA.fapply TLA.Succ 0))
(arith.add e
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_dunde_1a) (TLA.bAll a_Qunde_1a ((aa) (a_h16e0669e214bafdd37b2de01746035a aa
a_dunde_1a)))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v. (a_hd4a7fa801d94bc2a9c69d39a405ea2a(b_1, v)=((b_1=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b_1 <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (b_1 +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, v)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), (b_1 +  -.(1))), (\<lambda>d_1. bAll(Q_1, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d_1)))))))))))))))))" (is "?z_hj")
 using v'98 by blast
 have z_Hf:"(w \\in Value)" (is "?z_hf")
 using w_in by blast
 have z_Hk:"(e \\in Ballot)" (is "?z_hk")
 using v'99 by blast
 assume z_Hl:"(a_hd4a7fa801d94bc2a9c69d39a405ea2a(e, w)~=((e=0)|bEx(Quorum, (\<lambda>a_Qunde_1a. (bAll(a_Qunde_1a, (\<lambda>aa. (e <= (a_maxBalhash_primea[aa]))))&bEx(isa'dotdot( -.(1), (e +  -.(1))), (\<lambda>a_cunde_1a. (((a_cunde_1a~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_cunde_1a, w)&bAll(a_Qunde_1a, (\<lambda>aa. bAll(Value, (\<lambda>a_wunde_1a. (a_hedffe1caafe019043ade750241d505a(aa, a_cunde_1a, a_wunde_1a)=>(a_wunde_1a=w))))))))&bAll(isa'dotdot((a_cunde_1a + 1), (e +  -.(1))), (\<lambda>a_dunde_1a. bAll(a_Qunde_1a, (\<lambda>aa. a_h16e0669e214bafdd37b2de01746035a(aa, a_dunde_1a)))))))))))))" (is "?z_hcn~=?z_hco")
 have z_Hdz_z_Hj: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v. (a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (x <= (a_maxBalhash_primea[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, v)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=v))))))))&bAll(isa'dotdot((a_ca_1 + 1), (x +  -.(1))), (\<lambda>d_1. bAll(Q_1, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d_1))))))))))))))))) == ?z_hj" (is "?z_hdz == _")
 by (unfold bAll_def)
 have z_Hdz: "?z_hdz" (is "\\A x : ?z_hew(x)")
 by (unfold z_Hdz_z_Hj, fact z_Hj)
 have z_Hex: "?z_hew(e)" (is "_=>?z_hey")
 by (rule zenon_all_0 [of "?z_hew" "e", OF z_Hdz])
 show FALSE
 proof (rule zenon_imply [OF z_Hex])
  assume z_Hez:"(~?z_hk)"
  show FALSE
  by (rule notE [OF z_Hez z_Hk])
 next
  assume z_Hey:"?z_hey"
  have z_Hfa_z_Hey: "(\\A x:((x \\in Value)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(e, x)=((e=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>aa. (e <= (a_maxBalhash_primea[aa]))))&bEx(isa'dotdot( -.(1), (e +  -.(1))), (\<lambda>a_ca_1. (((a_ca_1~= -.(1))=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a(a_ca_1, x)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w_1. (a_hedffe1caafe019043ade750241d505a(a, a_ca_1, w_1)=>(w_1=x))))))))&bAll(isa'dotdot((a_ca_1 + 1), (e +  -.(1))), (\<lambda>d_1. bAll(Q_1, (\<lambda>a. a_h16e0669e214bafdd37b2de01746035a(a, d_1))))))))))))))) == ?z_hey" (is "?z_hfa == _")
  by (unfold bAll_def)
  have z_Hfa: "?z_hfa" (is "\\A x : ?z_hfy(x)")
  by (unfold z_Hfa_z_Hey, fact z_Hey)
  have z_Hfz: "?z_hfy(w)" (is "_=>?z_hga")
  by (rule zenon_all_0 [of "?z_hfy" "w", OF z_Hfa])
  show FALSE
  proof (rule zenon_imply [OF z_Hfz])
   assume z_Hgb:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hgb z_Hf])
  next
   assume z_Hga:"?z_hga"
   show FALSE
   by (rule notE [OF z_Hl z_Hga])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 628"; *} qed
lemma ob'631:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'56: "(VInv)"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Nat))"
assumes v'59: "((BallotAction ((self), (b))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Nat))"
fixes w
assumes w_in : "(w \<in> (Value))"
assumes v'75: "(fapply (([ i \<in> (Nat)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (i)))) : ((((SafeAt ((j), (w)))) \<Rightarrow> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((j), (w)) :: c)))))]), ((0))))"
assumes v'76: "((\<And> d :: c. d \<in> (Nat) \<Longrightarrow> ((fapply (([ i \<in> (Nat)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (i)))) : ((((SafeAt ((j), (w)))) \<Rightarrow> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((j), (w)) :: c)))))]), (d))) \<Longrightarrow> (fapply (([ i \<in> (Nat)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (i)))) : ((((SafeAt ((j), (w)))) \<Rightarrow> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((j), (w)) :: c)))))]), ((arith_add ((d), ((Succ[0]))))))))))"
assumes v'77: "(\<forall>f : ((((fapply ((f), ((0)))) & (\<forall> n \<in> (Nat) : (((fapply ((f), (n))) \<Rightarrow> (fapply ((f), ((arith_add ((n), ((Succ[0]))))))))))) \<Rightarrow> (\<forall> n \<in> (Nat) : (fapply ((f), (n)))))))"
shows "(\<forall> d \<in> (Nat) : (fapply (([ i \<in> (Nat)  \<mapsto> (\<forall> j \<in> ((isa_peri_peri_a (((0)), (i)))) : ((((SafeAt ((j), (w)))) \<Rightarrow> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((j), (w)) :: c)))))]), (d))))"(is "PROP ?ob'631")
proof -
ML_command {* writeln "*** TLAPS ENTER 631"; *}
show "PROP ?ob'631"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_a7c644.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_a7c644.znn.out
;; obligation #631
$hyp "v'56" VInv
$hyp "self_in" (TLA.in self Acceptor)
$hyp "b_in" (TLA.in b arith.N)
$hyp "v'59" (BallotAction self
b)
$hyp "a_ca_in" (TLA.in a_ca arith.N)
$hyp "w_in" (TLA.in w Value)
$hyp "v'75" (TLA.fapply (TLA.Fcn arith.N ((i) (TLA.bAll (arith.intrange 0
i) ((j) (=> (SafeAt j w) (a_hd4a7fa801d94bc2a9c69d39a405ea2a j
w)))))) 0)
$hyp "v'76" (TLA.bAll arith.N ((d) (=> (TLA.fapply (TLA.Fcn arith.N ((i) (TLA.bAll (arith.intrange 0
i) ((j) (=> (SafeAt j w) (a_hd4a7fa801d94bc2a9c69d39a405ea2a j
w)))))) d) (TLA.fapply (TLA.Fcn arith.N ((i) (TLA.bAll (arith.intrange 0
i) ((j) (=> (SafeAt j w) (a_hd4a7fa801d94bc2a9c69d39a405ea2a j
w)))))) (arith.add d
(TLA.fapply TLA.Succ 0))))))
$hyp "v'77" (A. ((f) (=> (/\ (TLA.fapply f 0)
(TLA.bAll arith.N ((n) (=> (TLA.fapply f n) (TLA.fapply f (arith.add n
(TLA.fapply TLA.Succ 0)))))))
(TLA.bAll arith.N ((n) (TLA.fapply f n))))))
$goal (TLA.bAll arith.N ((d) (TLA.fapply (TLA.Fcn arith.N ((i) (TLA.bAll (arith.intrange 0
i) ((j) (=> (SafeAt j w) (a_hd4a7fa801d94bc2a9c69d39a405ea2a j
w)))))) d)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hi:"(\\A f:(((f[0])&bAll(Nat, (\<lambda>n. ((f[n])=>(f[(n + 1)])))))=>bAll(Nat, (\<lambda>n. (f[n])))))" (is "\\A x : ?z_hba(x)")
 using v'77 by blast
 have z_Hg:"(Fcn(Nat, (\<lambda>i. bAll(isa'dotdot(0, i), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w))))))[0])" (is "?z_hg")
 using v'75 by blast
 have z_Hh:"bAll(Nat, (\<lambda>d. ((Fcn(Nat, (\<lambda>i. bAll(isa'dotdot(0, i), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w))))))[d])=>(Fcn(Nat, (\<lambda>i. bAll(isa'dotdot(0, i), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w))))))[(d + 1)]))))" (is "?z_hh")
 using v'76 by blast
 assume z_Hj:"(~bAll(Nat, (\<lambda>d. (Fcn(Nat, (\<lambda>i. bAll(isa'dotdot(0, i), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w))))))[d]))))" (is "~?z_hbs")
 have z_Hbu: "?z_hba(Fcn(Nat, (\<lambda>i. bAll(isa'dotdot(0, i), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w)))))))" (is "?z_hbv=>_")
 by (rule zenon_all_0 [of "?z_hba" "Fcn(Nat, (\<lambda>i. bAll(isa'dotdot(0, i), (\<lambda>j. (SafeAt(j, w)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(j, w))))))", OF z_Hi])
 show FALSE
 proof (rule zenon_imply [OF z_Hbu])
  assume z_Hbw:"(~?z_hbv)"
  show FALSE
  proof (rule zenon_notand [OF z_Hbw])
   assume z_Hbx:"(~?z_hg)"
   show FALSE
   by (rule notE [OF z_Hbx z_Hg])
  next
   assume z_Hby:"(~?z_hh)"
   show FALSE
   by (rule notE [OF z_Hby z_Hh])
  qed
 next
  assume z_Hbs:"?z_hbs"
  show FALSE
  by (rule notE [OF z_Hj z_Hbs])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 631"; *} qed
lemma ob'665:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'57: "(VInv)"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'60: "((BallotAction ((self), (b))))"
fixes a_a1a
assumes a_a1a_in : "(a_a1a \<in> (Acceptor))"
fixes a_a2a
assumes a_a2a_in : "(a_a2a \<in> (Acceptor))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes a_v1a
assumes a_v1a_in : "(a_v1a \<in> (Value))"
fixes a_v2a
assumes a_v2a_in : "(a_v2a \<in> (Value))"
assumes v'93: "(((fapply (((a_voteshash_primea :: c)), (self))) = (((fapply ((votes), (self))) \<union> ({(<<(b), (a_v1a)>>)})))))"
assumes v'94: "(((fapply (((a_voteshash_primea :: c)), (self))) = (((fapply ((votes), (self))) \<union> ({(<<(b), (a_v2a)>>)})))))"
shows "(((<<(b), (a_v1a)>>) \<in> (((fapply ((votes), (self))) \<union> ({(<<(b), (a_v2a)>>)})))))"(is "PROP ?ob'665")
proof -
ML_command {* writeln "*** TLAPS ENTER 665"; *}
show "PROP ?ob'665"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_caf8f5.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_caf8f5.znn.out
;; obligation #665
$hyp "v'57" VInv
$hyp "self_in" (TLA.in self Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'60" (BallotAction self
b)
$hyp "a_a1a_in" (TLA.in a_a1a Acceptor)
$hyp "a_a2a_in" (TLA.in a_a2a Acceptor)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "a_v1a_in" (TLA.in a_v1a Value)
$hyp "a_v2a_in" (TLA.in a_v2a Value)
$hyp "v'93" (= (TLA.fapply a_voteshash_primea self)
(TLA.cup (TLA.fapply votes self) (TLA.set (TLA.tuple b
a_v1a))))
$hyp "v'94" (= (TLA.fapply a_voteshash_primea self)
(TLA.cup (TLA.fapply votes self) (TLA.set (TLA.tuple b
a_v2a))))
$goal (TLA.in (TLA.tuple b a_v1a) (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b
a_v2a))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hk:"((a_voteshash_primea[self])=((votes[self]) \\cup {<<b, a_v2a>>}))" (is "?z_hm=?z_hp")
 using v'94 by blast
 have z_Hj:"(?z_hm=((votes[self]) \\cup {<<b, a_v1a>>}))" (is "_=?z_hw")
 using v'93 by blast
 assume z_Hl:"(~(<<b, a_v1a>> \\in ?z_hp))" (is "~?z_hba")
 have z_Hbb: "(\\A zenon_Vi:((zenon_Vi \\in ?z_hm)<=>(zenon_Vi \\in ?z_hp)))" (is "\\A x : ?z_hbg(x)")
 by (rule zenon_setequal_0 [of "?z_hm" "?z_hp", OF z_Hk])
 have z_Hbh: "?z_hbg(<<b, a_v1a>>)" (is "?z_hbi<=>_")
 by (rule zenon_all_0 [of "?z_hbg" "<<b, a_v1a>>", OF z_Hbb])
 show FALSE
 proof (rule zenon_equiv [OF z_Hbh])
  assume z_Hbj:"(~?z_hbi)"
  assume z_Hl:"(~?z_hba)"
  have z_Hbk: "(~(<<b, a_v1a>> \\in ?z_hw))" (is "~?z_hbl")
  by (rule subst [where P="(\<lambda>zenon_Vg. (~(<<b, a_v1a>> \\in zenon_Vg)))", OF z_Hj z_Hbj])
  have z_Hbq: "(~(<<b, a_v1a>> \\in {<<b, a_v1a>>}))" (is "~?z_hbr")
  by (rule zenon_notin_cup_1 [of "<<b, a_v1a>>" "(votes[self])" "{<<b, a_v1a>>}", OF z_Hbk])
  have z_Hbs: "(<<b, a_v1a>>~=<<b, a_v1a>>)" (is "?z_hy~=_")
  by (rule zenon_notin_addElt_0 [of "?z_hy" "?z_hy" "{}", OF z_Hbq])
  show FALSE
  by (rule zenon_noteq [OF z_Hbs])
 next
  assume z_Hbi:"?z_hbi"
  assume z_Hba:"?z_hba"
  show FALSE
  by (rule notE [OF z_Hl z_Hba])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 665"; *} qed
lemma ob'694:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'57: "(VInv)"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'60: "((BallotAction ((self), (b))))"
fixes a
assumes a_in : "(a \<in> (Acceptor))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
fixes v
assumes v_in : "(v \<in> (Value))"
assumes v'88: "(((less ((fapply (((a_maxBalhash_primea :: c)), (a))), (a_ca)))) & ((~ ((a_h16e0669e214bafdd37b2de01746035a ((a), (a_ca)) :: c)))))"
assumes v'89: "(((fapply (((a_maxBalhash_primea :: c)), (a))) = (a_ca)))"
assumes v'90: "((~ ((less ((a_ca), (a_ca))))))"
shows "(FALSE)"(is "PROP ?ob'694")
proof -
ML_command {* writeln "*** TLAPS ENTER 694"; *}
show "PROP ?ob'694"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_5870ad.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_5870ad.znn.out
;; obligation #694
$hyp "v'57" VInv
$hyp "self_in" (TLA.in self Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'60" (BallotAction self
b)
$hyp "a_in" (TLA.in a Acceptor)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "v_in" (TLA.in v Value)
$hyp "v'88" (/\ (arith.lt (TLA.fapply a_maxBalhash_primea a) a_ca)
(-. (a_h16e0669e214bafdd37b2de01746035a a
a_ca)))
$hyp "v'89" (= (TLA.fapply a_maxBalhash_primea a)
a_ca)
$hyp "v'90" (-. (arith.lt a_ca
a_ca))
$goal F.
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hi:"((a_maxBalhash_primea[a])=a_ca)" (is "?z_hl=_")
 using v'89 by blast
 have z_Hh:"((?z_hl < a_ca)&(~a_h16e0669e214bafdd37b2de01746035a(a, a_ca)))" (is "?z_hp&?z_hq")
 using v'88 by blast
 have z_Hj:"(~(a_ca < a_ca))" (is "~?z_hs")
 using v'90 by blast
 assume z_Hk:"(~FALSE)" (is "~?z_ht")
 have z_Hp: "?z_hp"
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hu: "(~?z_hp)"
 by (rule ssubst [where P="(\<lambda>zenon_Vf. (~(zenon_Vf < a_ca)))", OF z_Hi z_Hj])
 show FALSE
 by (rule notE [OF z_Hu z_Hp])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 694"; *} qed
lemma ob'749:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
assumes v'93: "(((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a)))"
assumes v'95: "((\<And> self :: c. self \<in> (Acceptor) \<Longrightarrow> (\<And> b :: c. b \<in> (Ballot) \<Longrightarrow> (((BallotAction ((self), (b)))) \<Longrightarrow> (((a_Cexcl_Nexta) \<or> ((((hc866a8a12a7524f0dc4faa03b3257b :: c)) = (a_Cexcl_varsa)))))))))"
assumes v'96: "((((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))) & ((((((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h9c328584958d15e5963012a5e014e1a :: c)))) \<and> ((a_hde69b2e11a77e40b5c91b849e88685a :: c)))) \<and> ((a_hfb87cccee30646b4043b294bd10930a :: c)))) & (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))))"
assumes v'97: "((((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))) \<Longrightarrow> (((a_Cexcl_Nexta) \<or> ((((hc866a8a12a7524f0dc4faa03b3257b :: c)) = (a_Cexcl_varsa)))))))"
assumes v'98: "(((TypeOK) \<Rightarrow> (((Next) = (\<exists> self \<in> (Acceptor) : (\<exists> b \<in> (Ballot) : ((BallotAction ((self), (b))))))))))"
shows "(((a_Cexcl_Nexta) \<or> ((((hc866a8a12a7524f0dc4faa03b3257b :: c)) = (a_Cexcl_varsa)))))"(is "PROP ?ob'749")
proof -
ML_command {* writeln "*** TLAPS ENTER 749"; *}
show "PROP ?ob'749"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_c159af.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_c159af.znn.out
;; obligation #749
$hyp "v'93" (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a)
a_VInv4a)
$hyp "v'95" (TLA.bAll Acceptor ((self) (TLA.bAll Ballot ((b) (=> (BallotAction self
b) (\/ a_Cexcl_Nexta (= hc866a8a12a7524f0dc4faa03b3257b
a_Cexcl_varsa)))))))
$hyp "v'96" (/\ (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a) a_VInv4a)
(/\ (/\ (/\ a_hef12f5554781c2213604492856f635a
a_h9c328584958d15e5963012a5e014e1a) a_hde69b2e11a77e40b5c91b849e88685a)
a_hfb87cccee30646b4043b294bd10930a) (\/ Next
(= a_h4fd5f73954dc53af536c1c75068837a
vars)))
$hyp "v'97" (=> (= a_h4fd5f73954dc53af536c1c75068837a vars) (\/ a_Cexcl_Nexta
(= hc866a8a12a7524f0dc4faa03b3257b a_Cexcl_varsa)))
$hyp "v'98" (=> TypeOK (= Next
(TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((b) (BallotAction self
b)))))))
$goal (\/ a_Cexcl_Nexta (= hc866a8a12a7524f0dc4faa03b3257b
a_Cexcl_varsa))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"bAll(Acceptor, (\<lambda>self. bAll(Ballot, (\<lambda>b. (BallotAction(self, b)=>(a_Cexcl_Nexta|(hc866a8a12a7524f0dc4faa03b3257b=a_Cexcl_varsa)))))))" (is "?z_hb")
 using v'95 by blast
 have z_He:"(TypeOK=>(Next=bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b. BallotAction(self, b)))))))" (is "_=>?z_hv")
 using v'98 by blast
 have z_Hd:"((a_h4fd5f73954dc53af536c1c75068837a=vars)=>(a_Cexcl_Nexta|(hc866a8a12a7524f0dc4faa03b3257b=a_Cexcl_varsa)))" (is "?z_hbb=>?z_hp")
 using v'97 by blast
 have z_Hc:"((((TypeOK&a_VInv2a)&a_VInv3a)&a_VInv4a)&((((a_hef12f5554781c2213604492856f635a&a_h9c328584958d15e5963012a5e014e1a)&a_hde69b2e11a77e40b5c91b849e88685a)&a_hfb87cccee30646b4043b294bd10930a)&(Next|?z_hbb)))" (is "?z_ha&?z_hbj")
 using v'96 by blast
 assume z_Hf:"(~?z_hp)" (is "~(_|?z_hr)")
 have z_Hbs_z_Hb: "(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>b. (BallotAction(x, b)=>?z_hp))))) == ?z_hb" (is "?z_hbs == _")
 by (unfold bAll_def)
 have z_Hbs: "?z_hbs" (is "\\A x : ?z_hca(x)")
 by (unfold z_Hbs_z_Hb, fact z_Hb)
 have z_Ha: "?z_ha" (is "?z_hbe&_")
 by (rule zenon_and_0 [OF z_Hc])
 have z_Hbj: "?z_hbj" (is "?z_hbk&?z_hbr")
 by (rule zenon_and_1 [OF z_Hc])
 have z_Hbr: "?z_hbr"
 by (rule zenon_and_1 [OF z_Hbj])
 have z_Hbe: "?z_hbe" (is "?z_hbf&_")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbf: "?z_hbf"
 by (rule zenon_and_0 [OF z_Hbe])
 have z_Hu: "TypeOK"
 by (rule zenon_and_0 [OF z_Hbf])
 have z_Hcb: "(~a_Cexcl_Nexta)"
 by (rule zenon_notor_0 [OF z_Hf])
 have z_Hcc: "(hc866a8a12a7524f0dc4faa03b3257b~=a_Cexcl_varsa)"
 by (rule zenon_notor_1 [OF z_Hf])
 show FALSE
 proof (rule zenon_or [OF z_Hbr])
  assume z_Hw:"Next"
  show FALSE
  proof (rule zenon_imply [OF z_He])
   assume z_Hcd:"(~TypeOK)"
   show FALSE
   by (rule notE [OF z_Hcd z_Hu])
  next
   assume z_Hv:"?z_hv" (is "_=?z_hx")
   have z_Hce_z_Hv: "(Next=(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b)))))) == ?z_hv" (is "?z_hce == _")
   by (unfold bEx_def)
   have z_Hce: "?z_hce" (is "_=?z_hcf")
   by (unfold z_Hce_z_Hv, fact z_Hv)
   have z_Hcj: "(TRUE=?z_hcf)" (is "?z_hck=_")
   by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vba. (zenon_Vba=?z_hcf))" "Next", OF z_Hce z_Hw])
   have z_Hcf: "?z_hcf" (is "\\E x : ?z_hco(x)")
   by (rule zenon_eq_true_x_0 [of "?z_hcf", OF z_Hcj])
   have z_Hcp: "?z_hco((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))))" (is "?z_hcr&?z_hcs")
   by (rule zenon_ex_choose_0 [of "?z_hco", OF z_Hcf])
   have z_Hcr: "?z_hcr"
   by (rule zenon_and_0 [OF z_Hcp])
   have z_Hcs: "?z_hcs"
   by (rule zenon_and_1 [OF z_Hcp])
   have z_Hct_z_Hcs: "(\\E x:((x \\in Ballot)&BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x))) == ?z_hcs" (is "?z_hct == _")
   by (unfold bEx_def)
   have z_Hct: "?z_hct" (is "\\E x : ?z_hcx(x)")
   by (unfold z_Hct_z_Hcs, fact z_Hcs)
   have z_Hcy: "?z_hcx((CHOOSE x:((x \\in Ballot)&BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x))))" (is "?z_hda&?z_hdb")
   by (rule zenon_ex_choose_0 [of "?z_hcx", OF z_Hct])
   have z_Hda: "?z_hda"
   by (rule zenon_and_0 [OF z_Hcy])
   have z_Hdb: "?z_hdb"
   by (rule zenon_and_1 [OF z_Hcy])
   have z_Hdc: "?z_hca((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))))" (is "_=>?z_hdd")
   by (rule zenon_all_0 [of "?z_hca" "(CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b)))))", OF z_Hbs])
   show FALSE
   proof (rule zenon_imply [OF z_Hdc])
    assume z_Hde:"(~?z_hcr)"
    show FALSE
    by (rule notE [OF z_Hde z_Hcr])
   next
    assume z_Hdd:"?z_hdd"
    have z_Hdf_z_Hdd: "(\\A x:((x \\in Ballot)=>(BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x)=>?z_hp))) == ?z_hdd" (is "?z_hdf == _")
    by (unfold bAll_def)
    have z_Hdf: "?z_hdf" (is "\\A x : ?z_hdi(x)")
    by (unfold z_Hdf_z_Hdd, fact z_Hdd)
    have z_Hdj: "?z_hdi((CHOOSE x:((x \\in Ballot)&BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x))))" (is "_=>?z_hdk")
    by (rule zenon_all_0 [of "?z_hdi" "(CHOOSE x:((x \\in Ballot)&BallotAction((CHOOSE x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b. BallotAction(x, b))))), x)))", OF z_Hdf])
    show FALSE
    proof (rule zenon_imply [OF z_Hdj])
     assume z_Hdl:"(~?z_hda)"
     show FALSE
     by (rule notE [OF z_Hdl z_Hda])
    next
     assume z_Hdk:"?z_hdk"
     show FALSE
     proof (rule zenon_imply [OF z_Hdk])
      assume z_Hdm:"(~?z_hdb)"
      show FALSE
      by (rule notE [OF z_Hdm z_Hdb])
     next
      assume z_Hp:"?z_hp"
      show FALSE
      proof (rule zenon_or [OF z_Hp])
       assume z_Hq:"a_Cexcl_Nexta"
       show FALSE
       by (rule notE [OF z_Hcb z_Hq])
      next
       assume z_Hr:"?z_hr"
       show FALSE
       by (rule notE [OF z_Hcc z_Hr])
      qed
     qed
    qed
   qed
  qed
 next
  assume z_Hbb:"?z_hbb"
  show FALSE
  proof (rule zenon_imply [OF z_Hd])
   assume z_Hdn:"(a_h4fd5f73954dc53af536c1c75068837a~=vars)"
   show FALSE
   by (rule notE [OF z_Hdn z_Hbb])
  next
   assume z_Hp:"?z_hp"
   show FALSE
   proof (rule zenon_or [OF z_Hp])
    assume z_Hq:"a_Cexcl_Nexta"
    show FALSE
    by (rule notE [OF z_Hcb z_Hq])
   next
    assume z_Hr:"?z_hr"
    show FALSE
    by (rule notE [OF z_Hcc z_Hr])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 749"; *} qed
lemma ob'435:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'52: "(((((((TypeOK) \<and> (\<forall> a \<in> (Acceptor) : (\<forall> b \<in> (Ballot) : (\<forall> v \<in> (Value) : (((((<<(b), (v)>>) \<in> (fapply ((votes), (a))))) \<Rightarrow> (fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Ballot)  \<mapsto> ((((bb) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a_1 \<in> (Q) : ((geq ((fapply ((maxBal), (a_1))), (bb))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((SA), (a_ca))) & (\<forall> a_1 \<in> (Q) : (\<forall> w \<in> (Value) : (((((<<(a_ca), (w)>>) \<in> (fapply ((votes), (a_1))))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : (\<forall> a_1 \<in> (Q) : (\<forall> v_1 \<in> (Value) : ((~ (((<<(d), (v_1)>>) \<in> (fapply ((votes), (a_1)))))))))))))))]))))), (b)))))))))) \<and> (a_VInv3a))) \<and> (a_VInv4a)))"
assumes v'53: "(((<<((a_voteshash_primea :: c)), ((a_maxBalhash_primea :: c))>>) = (<<(votes), (maxBal)>>)))"
shows "(\<forall> a \<in> (Acceptor) : (\<forall> b \<in> (Ballot) : (\<forall> v \<in> (Value) : (((((<<(b), (v)>>) \<in> (fapply (((a_voteshash_primea :: c)), (a))))) \<Rightarrow> (fapply ((Choice(%SA. (((SA) = ([ bb \<in> (Ballot)  \<mapsto> ((((bb) = ((0)))) | (\<exists> Q \<in> (Quorum) : ((\<forall> a_1 \<in> (Q) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (a_1))), (bb))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> ((fapply ((SA), (a_ca))) & (\<forall> a_1 \<in> (Q) : (\<forall> w \<in> (Value) : (((((<<(a_ca), (w)>>) \<in> (fapply (((a_voteshash_primea :: c)), (a_1))))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((bb), ((minus (((Succ[0]))))))))))) : (\<forall> a_1 \<in> (Q) : (\<forall> v_1 \<in> (Value) : ((~ (((<<(d), (v_1)>>) \<in> (fapply (((a_voteshash_primea :: c)), (a_1)))))))))))))))]))))), (b))))))))"(is "PROP ?ob'435")
proof -
ML_command {* writeln "*** TLAPS ENTER 435"; *}
show "PROP ?ob'435"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 435"; *} qed
lemma ob'820:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
assumes v'94: "(VInv)"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes v
assumes v_in : "(v \<in> (Value))"
assumes v'116: "((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) \<noteq> (chosen)))"
assumes v'117: "(((chosen) \<subseteq> ((h7f4dc7fdc95ffefa185ce3d407a37f :: c))))"
shows "(\<exists> w \<in> ((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) : (((w) \<notin> (chosen))))"(is "PROP ?ob'820")
proof -
ML_command {* writeln "*** TLAPS ENTER 820"; *}
show "PROP ?ob'820"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_67e329.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_67e329.znn.out
;; obligation #820
$hyp "v'94" VInv
$hyp "self_in" (TLA.in self Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v_in" (TLA.in v Value)
$hyp "v'116" (-. (= h7f4dc7fdc95ffefa185ce3d407a37f
chosen))
$hyp "v'117" (TLA.subseteq chosen
h7f4dc7fdc95ffefa185ce3d407a37f)
$goal (TLA.bEx h7f4dc7fdc95ffefa185ce3d407a37f ((w) (-. (TLA.in w
chosen))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"(chosen \\subseteq h7f4dc7fdc95ffefa185ce3d407a37f)" (is "?z_hg")
 using v'117 by blast
 have zenon_L1_: "(~(\\A zenon_Vx:((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) ==> (~(\\E x:((x \\in h7f4dc7fdc95ffefa185ce3d407a37f)&(~(x \\in chosen))))) ==> (\\A x:((x \\in chosen)=>(x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) ==> FALSE" (is "?z_hk ==> ?z_hq ==> ?z_hw ==> FALSE")
 proof -
  assume z_Hk:"?z_hk" (is "~(\\A x : ?z_hy(x))")
  assume z_Hq:"?z_hq" (is "~(\\E x : ?z_hz(x))")
  assume z_Hw:"?z_hw" (is "\\A x : ?z_hba(x)")
  have z_Hbb: "(\\E zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))" (is "\\E x : ?z_hbd(x)")
  by (rule zenon_notallex_0 [of "?z_hy", OF z_Hk])
  have z_Hbe: "?z_hbd((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))))" (is "~(?z_hbg<=>?z_hbh)")
  by (rule zenon_ex_choose_0 [of "?z_hbd", OF z_Hbb])
  show FALSE
  proof (rule zenon_notequiv [OF z_Hbe])
   assume z_Hbi:"(~?z_hbg)"
   assume z_Hbh:"?z_hbh"
   have z_Hbj: "?z_hba((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))))"
   by (rule zenon_all_0 [of "?z_hba" "(CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))", OF z_Hw])
   show FALSE
   proof (rule zenon_imply [OF z_Hbj])
    assume z_Hbk:"(~?z_hbh)"
    show FALSE
    by (rule notE [OF z_Hbk z_Hbh])
   next
    assume z_Hbg:"?z_hbg"
    show FALSE
    by (rule notE [OF z_Hbi z_Hbg])
   qed
  next
   assume z_Hbg:"?z_hbg"
   assume z_Hbk:"(~?z_hbh)"
   have z_Hbl: "~?z_hz((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))))" (is "~(_&?z_hbk)")
   by (rule zenon_notex_0 [of "?z_hz" "(CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))", OF z_Hq])
   show FALSE
   proof (rule zenon_notand [OF z_Hbl])
    assume z_Hbi:"(~?z_hbg)"
    show FALSE
    by (rule notE [OF z_Hbi z_Hbg])
   next
    assume z_Hbm:"(~?z_hbk)"
    show FALSE
    by (rule notE [OF z_Hbm z_Hbk])
   qed
  qed
 qed
 assume z_Hh:"(~bEx(h7f4dc7fdc95ffefa185ce3d407a37f, (\<lambda>w. (~(w \\in chosen)))))" (is "~?z_hbn")
 have z_Hbs_z_Hg: "bAll(chosen, (\<lambda>x. (x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) == ?z_hg" (is "?z_hbs == _")
 by (unfold subset_def)
 have z_Hbs: "?z_hbs"
 by (unfold z_Hbs_z_Hg, fact z_Hg)
 have z_Hw_z_Hbs: "(\\A x:((x \\in chosen)=>(x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) == ?z_hbs" (is "?z_hw == _")
 by (unfold bAll_def)
 have z_Hw: "?z_hw" (is "\\A x : ?z_hba(x)")
 by (unfold z_Hw_z_Hbs, fact z_Hbs)
 have z_Hq_z_Hh: "(~(\\E x:((x \\in h7f4dc7fdc95ffefa185ce3d407a37f)&(~(x \\in chosen))))) == (~?z_hbn)" (is "?z_hq == ?z_hh")
 by (unfold bEx_def)
 have z_Hq: "?z_hq" (is "~(\\E x : ?z_hz(x))")
 by (unfold z_Hq_z_Hh, fact z_Hh)
 have z_Hk: "(~(\\A zenon_Vx:((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))" (is "~(\\A x : ?z_hy(x))")
 by (rule zenon_notsetequal_0 [of "h7f4dc7fdc95ffefa185ce3d407a37f" "chosen", OF z_Hf])
 show FALSE
 by (rule zenon_L1_ [OF z_Hk z_Hq z_Hw])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 820"; *} qed
lemma ob'446:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition BallotAction suppressed *)
assumes v'54: "((((((((((votes) \<in> ([(Acceptor) \<rightarrow> ((SUBSET (((Ballot) \<times> (Value)))))]))) & (((maxBal) \<in> ([(Acceptor) \<rightarrow> (((Ballot) \<union> ({((minus (((Succ[0])))))})))])))) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a)))"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'57: "((BallotAction ((self), (b))))"
assumes v'66: "(\<exists> v \<in> (Value) : (((leq ((fapply ((maxBal), (self))), (b)))) & ((DidNotVoteIn ((self), (b)))) & (\<forall> p \<in> (((Acceptor) \\ ({(self)}))) : (\<forall> w \<in> (Value) : ((((VotedFor ((p), (b), (w)))) \<Rightarrow> (((w) = (v))))))) & ((SafeAt ((b), (v)))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (v)>>)})))]))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(self)] = (b)])))))"
shows "(((((a_voteshash_primea :: c)) \<in> ([(Acceptor) \<rightarrow> ((SUBSET (((Ballot) \<times> (Value)))))]))) & ((((a_maxBalhash_primea :: c)) \<in> ([(Acceptor) \<rightarrow> (((Ballot) \<union> ({((minus (((Succ[0])))))})))]))))"(is "PROP ?ob'446")
proof -
ML_command {* writeln "*** TLAPS ENTER 446"; *}
show "PROP ?ob'446"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 446"; *} qed
lemma ob'838:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'105: "(((Value) \<noteq> ({})))"
assumes v'106: "((TypeOK) & (a_VInv2a) & (a_VInv3a) & (\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (b))))))"
assumes v'107: "(\<forall> b_1 \<in> (Ballot) : (\<forall> v \<in> (Value) : ((((SafeAt ((b_1), (v)))) = ((((b_1) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply ((maxBal), (a))), (b_1))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v)))) & (\<forall> a \<in> (Q_1) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((DidNotVoteIn ((a), (d)))))))))))))))"
assumes v'108: "(((b) = ((0))))"
shows "(\<exists> v \<in> (Value) : ((SafeAt ((b), (v)))))"(is "PROP ?ob'838")
proof -
ML_command {* writeln "*** TLAPS ENTER 838"; *}
show "PROP ?ob'838"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_42c38a.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_42c38a.znn.out
;; obligation #838
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'105" (-. (= Value TLA.emptyset))
$hyp "v'106" (/\ TypeOK a_VInv2a a_VInv3a (TLA.bAll Q ((a) (arith.le b
(TLA.fapply maxBal a)))))
$hyp "v'107" (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v) (= (SafeAt b_1 v)
(\/ (= b_1 0) (TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le b_1
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q_1 ((a) (DidNotVoteIn a
d)))))))))))))))))
$hyp "v'108" (= b 0)
$goal (TLA.bEx Value ((v) (SafeAt b
v)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"(b=0)"
 using v'108 by blast
 have z_He:"bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v. (SafeAt(b_1, v)=((b_1=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b_1 <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b_1 +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b_1 +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))" (is "?z_he")
 using v'107 by blast
 have z_Hb:"(b \\in Ballot)" (is "?z_hb")
 using b_in by blast
 have z_Hc:"(Value~={})"
 using v'105 by blast
 assume z_Hg:"(~bEx(Value, (\<lambda>v. SafeAt(b, v))))" (is "~?z_hci")
 have z_Hcl_z_He: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v. (SafeAt(x, v)=((x=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))) == ?z_he" (is "?z_hcl == _")
 by (unfold bAll_def)
 have z_Hcl: "?z_hcl" (is "\\A x : ?z_hdi(x)")
 by (unfold z_Hcl_z_He, fact z_He)
 have z_Hdj_z_Hg: "(~(\\E x:((x \\in Value)&SafeAt(b, x)))) == (~?z_hci)" (is "?z_hdj == ?z_hg")
 by (unfold bEx_def)
 have z_Hdj: "?z_hdj" (is "~(\\E x : ?z_hdo(x))")
 by (unfold z_Hdj_z_Hg, fact z_Hg)
 have z_Hdp: "(0 \\in Ballot)" (is "?z_hdp")
 by (rule subst [where P="(\<lambda>zenon_Vfo. (zenon_Vfo \\in Ballot))", OF z_Hf z_Hb])
 have z_Hdt: "?z_hdi(0)" (is "_=>?z_hdu")
 by (rule zenon_all_0 [of "?z_hdi" "0", OF z_Hcl])
 show FALSE
 proof (rule zenon_imply [OF z_Hdt])
  assume z_Hdv:"(~?z_hdp)"
  show FALSE
  by (rule notE [OF z_Hdv z_Hdp])
 next
  assume z_Hdu:"?z_hdu"
  have z_Hdw_z_Hdu: "(\\A x:((x \\in Value)=>(SafeAt(0, x)=((0=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (0 <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (0 +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), (0 +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))) == ?z_hdu" (is "?z_hdw == _")
  by (unfold bAll_def)
  have z_Hdw: "?z_hdw" (is "\\A x : ?z_hey(x)")
  by (unfold z_Hdw_z_Hdu, fact z_Hdu)
  have z_Hez: "(~(\\A zenon_Vj:((zenon_Vj \\in Value)<=>(zenon_Vj \\in {}))))" (is "~(\\A x : ?z_hff(x))")
  by (rule zenon_notsetequal_0 [of "Value" "{}", OF z_Hc])
  have z_Hfg: "(\\E zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {}))))" (is "\\E x : ?z_hfi(x)")
  by (rule zenon_notallex_0 [of "?z_hff", OF z_Hez])
  have z_Hfj: "?z_hfi((CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {})))))" (is "~(?z_hfl<=>?z_hfm)")
  by (rule zenon_ex_choose_0 [of "?z_hfi", OF z_Hfg])
  show FALSE
  proof (rule zenon_notequiv [OF z_Hfj])
   assume z_Hfn:"(~?z_hfl)"
   assume z_Hfm:"?z_hfm"
   show FALSE
   by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {}))))", OF z_Hfm])
  next
   assume z_Hfl:"?z_hfl"
   assume z_Hfo:"(~?z_hfm)"
   have z_Hfp: "?z_hey((CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {})))))" (is "_=>?z_hfq")
   by (rule zenon_all_0 [of "?z_hey" "(CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {}))))", OF z_Hdw])
   show FALSE
   proof (rule zenon_imply [OF z_Hfp])
    assume z_Hfn:"(~?z_hfl)"
    show FALSE
    by (rule notE [OF z_Hfn z_Hfl])
   next
    assume z_Hfq:"?z_hfq" (is "?z_hfr=?z_hfs")
    show FALSE
    proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vjn. (?z_hfr=zenon_Vjn))" "(0=0)" "bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (0 <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (0 +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, (CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {})))))&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=(CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {}))))))))))))&bAll(isa'dotdot((a_ca + 1), (0 +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d)))))))))))", OF z_Hfq])
     assume z_Hgl:"(?z_hfs=TRUE)" (is "_=?z_hgm")
     assume z_Hgn:"(?z_hfr=?z_hgm)"
     have z_Hfr: "?z_hfr"
     by (rule zenon_eq_x_true_0 [of "?z_hfr", OF z_Hgn])
     have z_Hgo: "~?z_hdo((CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {})))))" (is "~(_&?z_hgp)")
     by (rule zenon_notex_0 [of "?z_hdo" "(CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {}))))", OF z_Hdj])
     show FALSE
     proof (rule zenon_notand [OF z_Hgo])
      assume z_Hfn:"(~?z_hfl)"
      show FALSE
      by (rule notE [OF z_Hfn z_Hfl])
     next
      assume z_Hgq:"(~?z_hgp)"
      have z_Hgr: "(~?z_hfr)"
      by (rule subst [where P="(\<lambda>zenon_Vzn. (~SafeAt(zenon_Vzn, (CHOOSE zenon_Vj:(~((zenon_Vj \\in Value)<=>(zenon_Vj \\in {})))))))", OF z_Hf z_Hgq])
      show FALSE
      by (rule notE [OF z_Hgr z_Hfr])
     qed
    next
     assume z_Hgw:"(?z_hfs=FALSE)" (is "_=?z_hgx")
     assume z_Hgy:"(?z_hfr=?z_hgx)"
     have z_Hgz: "(~?z_hfs)" (is "~(?z_heb|?z_hfw)")
     by (rule zenon_eq_x_false_0 [of "?z_hfs", OF z_Hgw])
     have z_Hha: "(0~=0)"
     by (rule zenon_notor_0 [OF z_Hgz])
     show FALSE
     by (rule zenon_noteq [OF z_Hha])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 838"; *} qed
lemma ob'845:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'106: "(\<exists> v \<in> (Value) : (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))"
fixes v
assumes v_in : "(v \<in> (Value))"
assumes v'112: "(\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d))))))))"
assumes v'113: "((((SafeAt ((b), (v)))) = ((((b) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply ((maxBal), (a))), (b))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v)))) & (\<forall> a \<in> (Q_1) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((DidNotVoteIn ((a), (d)))))))))))))"
assumes v'114: "((TypeOK) & (a_VInv2a) & (a_VInv3a) & (\<forall> a \<in> (Q) : ((geq ((fapply ((maxBal), (a))), (b))))))"
assumes v'115: "(((b) \<noteq> ((0))))"
shows "((SafeAt ((b), (v))))"(is "PROP ?ob'845")
proof -
ML_command {* writeln "*** TLAPS ENTER 845"; *}
show "PROP ?ob'845"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_da98ba.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_da98ba.znn.out
;; obligation #845
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'106" (TLA.bEx Value ((v) (TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))
$hyp "v_in" (TLA.in v Value)
$hyp "v'112" (TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))
$hyp "v'113" (= (SafeAt b v) (\/ (= b 0)
(TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le b
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q_1 ((a) (DidNotVoteIn a
d)))))))))))))
$hyp "v'114" (/\ TypeOK a_VInv2a a_VInv3a (TLA.bAll Q ((a) (arith.le b
(TLA.fapply maxBal a)))))
$hyp "v'115" (-. (= b 0))
$goal (SafeAt b
v)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"(TypeOK&(a_VInv2a&(a_VInv3a&bAll(Q, (\<lambda>a. (b <= (maxBal[a])))))))" (is "_&?z_hk")
 using v'114 by blast
 have z_Hf:"(SafeAt(b, v)=((b=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))" (is "?z_hw=?z_hy")
 using v'113 by blast
 have z_Ha:"(Q \\in Quorum)" (is "?z_ha")
 using Q_in by blast
 have z_He:"bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q, (\<lambda>a. DidNotVoteIn(a, d))))))))" (is "?z_he")
 using v'112 by blast
 assume z_Hi:"(~?z_hw)"
 have z_Hk: "?z_hk" (is "_&?z_hm")
 by (rule zenon_and_1 [OF z_Hg])
 have z_Hm: "?z_hm" (is "_&?z_ho")
 by (rule zenon_and_1 [OF z_Hk])
 have z_Ho: "?z_ho"
 by (rule zenon_and_1 [OF z_Hm])
 show FALSE
 proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vi. (?z_hw=zenon_Vi))" "(b=0)" "bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d)))))))))))", OF z_Hf])
  assume z_Hcv:"(?z_hy=TRUE)" (is "_=?z_hcw")
  assume z_Hcx:"(?z_hw=?z_hcw)"
  have z_Hw: "?z_hw"
  by (rule zenon_eq_x_true_0 [of "?z_hw", OF z_Hcx])
  show FALSE
  by (rule notE [OF z_Hi z_Hw])
 next
  assume z_Hcy:"(?z_hy=FALSE)" (is "_=?z_hcz")
  assume z_Hda:"(?z_hw=?z_hcz)"
  have z_Hdb: "(~?z_hy)" (is "~(?z_hz|?z_hbb)")
  by (rule zenon_eq_x_false_0 [of "?z_hy", OF z_Hcy])
  have z_Hdc: "(~?z_hbb)"
  by (rule zenon_notor_1 [OF z_Hdb])
  have z_Hdd_z_Hdc: "(~(\\E x:((x \\in Quorum)&(bAll(x, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(x, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(x, (\<lambda>a. DidNotVoteIn(a, d)))))))))))) == (~?z_hbb)" (is "?z_hdd == ?z_hdc")
  by (unfold bEx_def)
  have z_Hdd: "?z_hdd" (is "~(\\E x : ?z_hdt(x))")
  by (unfold z_Hdd_z_Hdc, fact z_Hdc)
  have z_Hdu: "~?z_hdt(Q)" (is "~(_&?z_hdv)")
  by (rule zenon_notex_0 [of "?z_hdt" "Q", OF z_Hdd])
  show FALSE
  proof (rule zenon_notand [OF z_Hdu])
   assume z_Hdw:"(~?z_ha)"
   show FALSE
   by (rule notE [OF z_Hdw z_Ha])
  next
   assume z_Hdx:"(~?z_hdv)"
   show FALSE
   proof (rule zenon_notand [OF z_Hdx])
    assume z_Hdy:"(~?z_ho)"
    show FALSE
    by (rule notE [OF z_Hdy z_Ho])
   next
    assume z_Hdz:"(~?z_he)"
    show FALSE
    by (rule notE [OF z_Hdz z_He])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 845"; *} qed
lemma ob'851:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'106: "(\<exists> v \<in> (Value) : (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v)))) & (\<forall> a \<in> (Q) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q) : ((DidNotVoteIn ((a), (d)))))))))"
fixes v
assumes v_in : "(v \<in> (Value))"
assumes v'113: "(\<forall> b_1 \<in> (Ballot) : (\<forall> v_1 \<in> (Value) : ((((SafeAt ((b_1), (v_1)))) = ((((b_1) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply ((maxBal), (a))), (b_1))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v_1)))) & (\<forall> a \<in> (Q_1) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v_1)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b_1), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((DidNotVoteIn ((a), (d)))))))))))))))"
shows "((((SafeAt ((b), (v)))) = ((((b) = ((0)))) | (\<exists> Q_1 \<in> (Quorum) : ((\<forall> a \<in> (Q_1) : ((geq ((fapply ((maxBal), (a))), (b))))) & (\<exists> a_ca \<in> ((isa_peri_peri_a (((minus (((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((((((a_ca) \<noteq> ((minus (((Succ[0]))))))) \<Rightarrow> (((SafeAt ((a_ca), (v)))) & (\<forall> a \<in> (Q_1) : (\<forall> w \<in> (Value) : ((((VotedFor ((a), (a_ca), (w)))) \<Rightarrow> (((w) = (v)))))))))) & (\<forall> d \<in> ((isa_peri_peri_a (((arith_add ((a_ca), ((Succ[0]))))), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<forall> a \<in> (Q_1) : ((DidNotVoteIn ((a), (d)))))))))))))"(is "PROP ?ob'851")
proof -
ML_command {* writeln "*** TLAPS ENTER 851"; *}
show "PROP ?ob'851"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_3c7703.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_3c7703.znn.out
;; obligation #851
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'106" (TLA.bEx Value ((v) (TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v)
(TLA.bAll Q ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w v))))))))
(TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q ((a) (DidNotVoteIn a
d))))))))))
$hyp "v_in" (TLA.in v Value)
$hyp "v'113" (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v_1) (= (SafeAt b_1
v_1) (\/ (= b_1 0)
(TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le b_1
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v_1)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w
v_1)))))))) (TLA.bAll (arith.intrange (arith.add a_ca
(TLA.fapply TLA.Succ 0)) (arith.add b_1
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q_1 ((a) (DidNotVoteIn a
d)))))))))))))))))
$goal (= (SafeAt b v) (\/ (= b 0)
(TLA.bEx Quorum ((Q_1) (/\ (TLA.bAll Q_1 ((a) (arith.le b
(TLA.fapply maxBal a))))
(TLA.bEx (arith.intrange (arith.minus (TLA.fapply TLA.Succ 0)) (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (=> (-. (= a_ca
(arith.minus (TLA.fapply TLA.Succ 0)))) (/\ (SafeAt a_ca v)
(TLA.bAll Q_1 ((a) (TLA.bAll Value ((w) (=> (VotedFor a a_ca w) (= w
v)))))))) (TLA.bAll (arith.intrange (arith.add a_ca (TLA.fapply TLA.Succ 0))
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bAll Q_1 ((a) (DidNotVoteIn a
d)))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v_1. (SafeAt(b_1, v_1)=((b_1=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b_1 <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b_1 +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v_1)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v_1))))))))&bAll(isa'dotdot((a_ca + 1), (b_1 +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))))))" (is "?z_he")
 using v'113 by blast
 have z_Hd:"(v \\in Value)" (is "?z_hd")
 using v_in by blast
 have z_Hb:"(b \\in Ballot)" (is "?z_hb")
 using b_in by blast
 assume z_Hf:"(SafeAt(b, v)~=((b=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d)))))))))))))" (is "?z_hch~=?z_hci")
 have z_Hdg_z_He: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v_1. (SafeAt(x, v_1)=((x=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (x <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (x +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, v_1)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=v_1))))))))&bAll(isa'dotdot((a_ca + 1), (x +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))))) == ?z_he" (is "?z_hdg == _")
 by (unfold bAll_def)
 have z_Hdg: "?z_hdg" (is "\\A x : ?z_hed(x)")
 by (unfold z_Hdg_z_He, fact z_He)
 have z_Hee: "?z_hed(b)" (is "_=>?z_hef")
 by (rule zenon_all_0 [of "?z_hed" "b", OF z_Hdg])
 show FALSE
 proof (rule zenon_imply [OF z_Hee])
  assume z_Heg:"(~?z_hb)"
  show FALSE
  by (rule notE [OF z_Heg z_Hb])
 next
  assume z_Hef:"?z_hef"
  have z_Heh_z_Hef: "(\\A x:((x \\in Value)=>(SafeAt(b, x)=((b=0)|bEx(Quorum, (\<lambda>Q_1. (bAll(Q_1, (\<lambda>a. (b <= (maxBal[a]))))&bEx(isa'dotdot( -.(1), (b +  -.(1))), (\<lambda>a_ca. (((a_ca~= -.(1))=>(SafeAt(a_ca, x)&bAll(Q_1, (\<lambda>a. bAll(Value, (\<lambda>w. (VotedFor(a, a_ca, w)=>(w=x))))))))&bAll(isa'dotdot((a_ca + 1), (b +  -.(1))), (\<lambda>d. bAll(Q_1, (\<lambda>a. DidNotVoteIn(a, d))))))))))))))) == ?z_hef" (is "?z_heh == _")
  by (unfold bAll_def)
  have z_Heh: "?z_heh" (is "\\A x : ?z_hfc(x)")
  by (unfold z_Heh_z_Hef, fact z_Hef)
  have z_Hfd: "?z_hfc(v)" (is "_=>?z_hfe")
  by (rule zenon_all_0 [of "?z_hfc" "v", OF z_Heh])
  show FALSE
  proof (rule zenon_imply [OF z_Hfd])
   assume z_Hff:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hff z_Hd])
  next
   assume z_Hfe:"?z_hfe"
   show FALSE
   by (rule notE [OF z_Hf z_Hfe])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 851"; *} qed
lemma ob'923:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'112: "((TypeOK) & (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))) & (\<forall> self \<in> (Q) : (((\<forall> a_ca \<in> (Ballot) : ((((greater ((a_ca), (b)))) \<Rightarrow> ((~ ((BallotAction ((self), (a_ca))))))))) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
assumes v'117: "(((TypeOK) \<Rightarrow> (((Next) = (\<exists> self \<in> (Acceptor) : (\<exists> b_1 \<in> (Ballot) : ((BallotAction ((self), (b_1))))))))))"
shows "((((\<exists> self \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : ((BallotAction ((self), (a_ca))))))) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"(is "PROP ?ob'923")
proof -
ML_command {* writeln "*** TLAPS ENTER 923"; *}
show "PROP ?ob'923"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_9a579b.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_9a579b.znn.out
;; obligation #923
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'112" (/\ TypeOK (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a vars))
(TLA.bAll Q ((self) (\/ (TLA.bAll Ballot ((a_ca) (=> (arith.lt b a_ca)
(-. (BallotAction self a_ca))))) (= a_h4fd5f73954dc53af536c1c75068837a
vars)))))
$hyp "v'117" (=> TypeOK (= Next
(TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((b_1) (BallotAction self
b_1)))))))
$goal (\/ (/\ (TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((a_ca) (BallotAction self
a_ca)))))) (= a_h4fd5f73954dc53af536c1c75068837a
vars))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hc:"(TypeOK&((Next|(a_h4fd5f73954dc53af536c1c75068837a=vars))&bAll(Q, (\<lambda>self. (bAll(Ballot, (\<lambda>a_ca. ((b < a_ca)=>(~BallotAction(self, a_ca)))))|(a_h4fd5f73954dc53af536c1c75068837a=vars))))))" (is "_&?z_hg")
 using v'112 by blast
 have z_Hd:"(TypeOK=>(Next=bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b_1. BallotAction(self, b_1)))))))" (is "_=>?z_hba")
 using v'117 by blast
 assume z_He:"(~(bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b_1. BallotAction(self, b_1)))))|(a_h4fd5f73954dc53af536c1c75068837a=vars)))" (is "~(?z_hbb|?z_hj)")
 have z_Hf: "TypeOK"
 by (rule zenon_and_0 [OF z_Hc])
 have z_Hg: "?z_hg" (is "?z_hh&?z_hm")
 by (rule zenon_and_1 [OF z_Hc])
 have z_Hh: "?z_hh"
 by (rule zenon_and_0 [OF z_Hg])
 have z_Hbj: "(~?z_hbb)"
 by (rule zenon_notor_0 [OF z_He])
 have z_Hbk: "(a_h4fd5f73954dc53af536c1c75068837a~=vars)"
 by (rule zenon_notor_1 [OF z_He])
 have z_Hbl_z_Hbj: "(~(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))) == (~?z_hbb)" (is "?z_hbl == ?z_hbj")
 by (unfold bEx_def)
 have z_Hbl: "?z_hbl" (is "~(\\E x : ?z_hbt(x))")
 by (unfold z_Hbl_z_Hbj, fact z_Hbj)
 show FALSE
 proof (rule zenon_or [OF z_Hh])
  assume z_Hi:"Next"
  show FALSE
  proof (rule zenon_imply [OF z_Hd])
   assume z_Hbu:"(~TypeOK)"
   show FALSE
   by (rule notE [OF z_Hbu z_Hf])
  next
   assume z_Hba:"?z_hba"
   have z_Hbv_z_Hba: "(Next=(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))) == ?z_hba" (is "?z_hbv == _")
   by (unfold bEx_def)
   have z_Hbv: "?z_hbv" (is "_=?z_hbm")
   by (unfold z_Hbv_z_Hba, fact z_Hba)
   have z_Hbw: "(TRUE=?z_hbm)" (is "?z_hbx=_")
   by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vv. (zenon_Vv=?z_hbm))" "Next", OF z_Hbv z_Hi])
   have z_Hbm: "?z_hbm"
   by (rule zenon_eq_true_x_0 [of "?z_hbm", OF z_Hbw])
   show FALSE
   by (rule notE [OF z_Hbl z_Hbm])
  qed
 next
  assume z_Hj:"?z_hj"
  show FALSE
  by (rule notE [OF z_Hbk z_Hj])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 923"; *} qed
lemma ob'929:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'112: "((TypeOK) & (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))) & (\<forall> self \<in> (Q) : (((\<forall> a_ca \<in> (Ballot) : ((((greater ((a_ca), (b)))) \<Rightarrow> ((~ ((BallotAction ((self), (a_ca))))))))) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
assumes v'120: "((\<exists> self \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : ((BallotAction ((self), (a_ca)))))) & (\<forall> self \<in> (Q) : (\<forall> a_ca \<in> (Ballot) : ((((greater ((a_ca), (b)))) \<Rightarrow> ((~ ((BallotAction ((self), (a_ca)))))))))))"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
assumes v'134: "((BallotAction ((self), (a_ca))))"
assumes v'135: "((((greater ((a_ca), (b)))) \<Leftrightarrow> ((~ ((leq ((a_ca), (b))))))))"
shows "(\<exists> self_1 \<in> (Acceptor) : (\<exists> a_ca_1 \<in> (Ballot) : (((BallotAction ((self_1), (a_ca_1)))) & (((((self_1) \<in> (Q))) \<Rightarrow> ((leq ((a_ca_1), (b)))))))))"(is "PROP ?ob'929")
proof -
ML_command {* writeln "*** TLAPS ENTER 929"; *}
show "PROP ?ob'929"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_67cf60.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_67cf60.znn.out
;; obligation #929
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'112" (/\ TypeOK (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a vars))
(TLA.bAll Q ((self) (\/ (TLA.bAll Ballot ((a_ca) (=> (arith.lt b a_ca)
(-. (BallotAction self a_ca))))) (= a_h4fd5f73954dc53af536c1c75068837a
vars)))))
$hyp "v'120" (/\ (TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((a_ca) (BallotAction self
a_ca))))) (TLA.bAll Q ((self) (TLA.bAll Ballot ((a_ca) (=> (arith.lt b a_ca)
(-. (BallotAction self
a_ca))))))))
$hyp "self_in" (TLA.in self Acceptor)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "v'134" (BallotAction self a_ca)
$hyp "v'135" (<=> (arith.lt b a_ca) (-. (arith.le a_ca
b)))
$goal (TLA.bEx Acceptor ((self_1) (TLA.bEx Ballot ((a_ca_1) (/\ (BallotAction self_1
a_ca_1) (=> (TLA.in self_1 Q) (arith.le a_ca_1
b)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>a_ca. BallotAction(self, a_ca)))))&bAll(Q, (\<lambda>self. bAll(Ballot, (\<lambda>a_ca. ((b < a_ca)=>(~BallotAction(self, a_ca))))))))" (is "?z_hj&?z_hr")
 using v'120 by blast
 have z_Hf:"(a_ca \\in Ballot)" (is "?z_hf")
 using a_ca_in by blast
 have z_Hg:"BallotAction(self, a_ca)" (is "?z_hg")
 using v'134 by blast
 have z_He:"(self \\in Acceptor)" (is "?z_he")
 using self_in by blast
 have z_Hh:"((b < a_ca)<=>(~(a_ca <= b)))" (is "?z_hx<=>?z_hba")
 using v'135 by blast
 assume z_Hi:"(~bEx(Acceptor, (\<lambda>self_1. bEx(Ballot, (\<lambda>a_ca_1. (BallotAction(self_1, a_ca_1)&((self_1 \\in Q)=>(a_ca_1 <= b))))))))" (is "~?z_hbc")
 have z_Hr: "?z_hr"
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hbn_z_Hr: "(\\A x:((x \\in Q)=>bAll(Ballot, (\<lambda>a_ca. ((b < a_ca)=>(~BallotAction(x, a_ca))))))) == ?z_hr" (is "?z_hbn == _")
 by (unfold bAll_def)
 have z_Hbn: "?z_hbn" (is "\\A x : ?z_hbw(x)")
 by (unfold z_Hbn_z_Hr, fact z_Hr)
 have z_Hbx_z_Hi: "(~(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>a_ca_1. (BallotAction(x, a_ca_1)&((x \\in Q)=>(a_ca_1 <= b)))))))) == (~?z_hbc)" (is "?z_hbx == ?z_hi")
 by (unfold bEx_def)
 have z_Hbx: "?z_hbx" (is "~(\\E x : ?z_hcg(x))")
 by (unfold z_Hbx_z_Hi, fact z_Hi)
 show FALSE
 proof (rule zenon_equiv [OF z_Hh])
  assume z_Hch:"(~?z_hx)"
  assume z_Hci:"(~?z_hba)" (is "~~?z_hbb")
  have z_Hbb: "?z_hbb"
  by (rule zenon_notnot_0 [OF z_Hci])
  have z_Hcj: "~?z_hcg(self)" (is "~(_&?z_hck)")
  by (rule zenon_notex_0 [of "?z_hcg" "self", OF z_Hbx])
  show FALSE
  proof (rule zenon_notand [OF z_Hcj])
   assume z_Hcl:"(~?z_he)"
   show FALSE
   by (rule notE [OF z_Hcl z_He])
  next
   assume z_Hcm:"(~?z_hck)"
   have z_Hcn_z_Hcm: "(~(\\E x:((x \\in Ballot)&(BallotAction(self, x)&((self \\in Q)=>(x <= b)))))) == (~?z_hck)" (is "?z_hcn == ?z_hcm")
   by (unfold bEx_def)
   have z_Hcn: "?z_hcn" (is "~(\\E x : ?z_hcw(x))")
   by (unfold z_Hcn_z_Hcm, fact z_Hcm)
   have z_Hcx: "~?z_hcw(a_ca)" (is "~(_&?z_hcy)")
   by (rule zenon_notex_0 [of "?z_hcw" "a_ca", OF z_Hcn])
   show FALSE
   proof (rule zenon_notand [OF z_Hcx])
    assume z_Hcz:"(~?z_hf)"
    show FALSE
    by (rule notE [OF z_Hcz z_Hf])
   next
    assume z_Hda:"(~?z_hcy)" (is "~(_&?z_hdb)")
    show FALSE
    proof (rule zenon_notand [OF z_Hda])
     assume z_Hz:"(~?z_hg)"
     show FALSE
     by (rule notE [OF z_Hz z_Hg])
    next
     assume z_Hdc:"(~?z_hdb)" (is "~(?z_hcu=>_)")
     have z_Hba: "?z_hba"
     by (rule zenon_notimply_1 [OF z_Hdc])
     show FALSE
     by (rule notE [OF z_Hba z_Hbb])
    qed
   qed
  qed
 next
  assume z_Hx:"?z_hx"
  assume z_Hba:"?z_hba" (is "~?z_hbb")
  have z_Hdd: "?z_hbw(self)" (is "?z_hcu=>?z_hu")
  by (rule zenon_all_0 [of "?z_hbw" "self", OF z_Hbn])
  show FALSE
  proof (rule zenon_imply [OF z_Hdd])
   assume z_Hde:"(~?z_hcu)"
   have z_Hcj: "~?z_hcg(self)" (is "~(_&?z_hck)")
   by (rule zenon_notex_0 [of "?z_hcg" "self", OF z_Hbx])
   show FALSE
   proof (rule zenon_notand [OF z_Hcj])
    assume z_Hcl:"(~?z_he)"
    show FALSE
    by (rule notE [OF z_Hcl z_He])
   next
    assume z_Hcm:"(~?z_hck)"
    have z_Hcn_z_Hcm: "(~(\\E x:((x \\in Ballot)&(BallotAction(self, x)&(?z_hcu=>(x <= b)))))) == (~?z_hck)" (is "?z_hcn == ?z_hcm")
    by (unfold bEx_def)
    have z_Hcn: "?z_hcn" (is "~(\\E x : ?z_hcw(x))")
    by (unfold z_Hcn_z_Hcm, fact z_Hcm)
    have z_Hcx: "~?z_hcw(a_ca)" (is "~(_&?z_hcy)")
    by (rule zenon_notex_0 [of "?z_hcw" "a_ca", OF z_Hcn])
    show FALSE
    proof (rule zenon_notand [OF z_Hcx])
     assume z_Hcz:"(~?z_hf)"
     show FALSE
     by (rule notE [OF z_Hcz z_Hf])
    next
     assume z_Hda:"(~?z_hcy)" (is "~(_&?z_hdb)")
     show FALSE
     proof (rule zenon_notand [OF z_Hda])
      assume z_Hz:"(~?z_hg)"
      show FALSE
      by (rule notE [OF z_Hz z_Hg])
     next
      assume z_Hdc:"(~?z_hdb)"
      have z_Hcu: "?z_hcu"
      by (rule zenon_notimply_0 [OF z_Hdc])
      show FALSE
      by (rule notE [OF z_Hde z_Hcu])
     qed
    qed
   qed
  next
   assume z_Hu:"?z_hu"
   have z_Hdf_z_Hu: "(\\A x:((x \\in Ballot)=>((b < x)=>(~BallotAction(self, x))))) == ?z_hu" (is "?z_hdf == _")
   by (unfold bAll_def)
   have z_Hdf: "?z_hdf" (is "\\A x : ?z_hdk(x)")
   by (unfold z_Hdf_z_Hu, fact z_Hu)
   have z_Hdl: "?z_hdk(a_ca)" (is "_=>?z_hw")
   by (rule zenon_all_0 [of "?z_hdk" "a_ca", OF z_Hdf])
   show FALSE
   proof (rule zenon_imply [OF z_Hdl])
    assume z_Hcz:"(~?z_hf)"
    show FALSE
    by (rule notE [OF z_Hcz z_Hf])
   next
    assume z_Hw:"?z_hw" (is "_=>?z_hz")
    show FALSE
    proof (rule zenon_imply [OF z_Hw])
     assume z_Hch:"(~?z_hx)"
     show FALSE
     by (rule notE [OF z_Hch z_Hx])
    next
     assume z_Hz:"?z_hz"
     show FALSE
     by (rule notE [OF z_Hz z_Hg])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 929"; *} qed
lemma ob'948:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'119: "((((((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))) \<and> (\<forall> a \<in> (Q) : ((leq ((fapply ((maxBal), (a))), (b))))))) & (((\<exists> self \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : (((BallotAction ((self), (a_ca)))) & (((((self) \<in> (Q))) \<Rightarrow> ((leq ((a_ca), (b))))))))) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))))"
assumes v'120: "(((TypeOK) \<Rightarrow> (((Next) = (\<exists> self \<in> (Acceptor) : (\<exists> b_1 \<in> (Ballot) : ((BallotAction ((self), (b_1))))))))))"
shows "(((((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))) = (((\<exists> self \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : ((BallotAction ((self), (a_ca)))))) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"(is "PROP ?ob'948")
proof -
ML_command {* writeln "*** TLAPS ENTER 948"; *}
show "PROP ?ob'948"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_a70b1f.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_a70b1f.znn.out
;; obligation #948
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'119" (/\ (/\ (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a) a_VInv4a)
(TLA.bAll Q ((a) (arith.le (TLA.fapply maxBal a) b))))
(\/ (TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((a_ca) (/\ (BallotAction self
a_ca) (=> (TLA.in self Q) (arith.le a_ca b)))))))
(= a_h4fd5f73954dc53af536c1c75068837a vars)))
$hyp "v'120" (=> TypeOK (= Next
(TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((b_1) (BallotAction self
b_1)))))))
$goal (= (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a vars))
(\/ (TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((a_ca) (BallotAction self
a_ca))))) (= a_h4fd5f73954dc53af536c1c75068837a
vars)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hc:"(((((TypeOK&a_VInv2a)&a_VInv3a)&a_VInv4a)&bAll(Q, (\<lambda>a. ((maxBal[a]) <= b))))&(bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>a_ca. (BallotAction(self, a_ca)&((self \\in Q)=>(a_ca <= b)))))))|(a_h4fd5f73954dc53af536c1c75068837a=vars)))" (is "?z_hf&?z_hv")
 using v'119 by blast
 have z_Hd:"(TypeOK=>(Next=bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b_1. BallotAction(self, b_1)))))))" (is "_=>?z_hbm")
 using v'120 by blast
 assume z_He:"((Next|(a_h4fd5f73954dc53af536c1c75068837a=vars))~=(bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b_1. BallotAction(self, b_1)))))|(a_h4fd5f73954dc53af536c1c75068837a=vars)))" (is "?z_hbu~=?z_hbv")
 have z_Hf: "?z_hf" (is "?z_hg&?z_hn")
 by (rule zenon_and_0 [OF z_Hc])
 have z_Hg: "?z_hg" (is "?z_hh&_")
 by (rule zenon_and_0 [OF z_Hf])
 have z_Hh: "?z_hh" (is "?z_hi&_")
 by (rule zenon_and_0 [OF z_Hg])
 have z_Hi: "?z_hi"
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hj: "TypeOK"
 by (rule zenon_and_0 [OF z_Hi])
 show FALSE
 proof (rule zenon_imply [OF z_Hd])
  assume z_Hbw:"(~TypeOK)"
  show FALSE
  by (rule notE [OF z_Hbw z_Hj])
 next
  assume z_Hbm:"?z_hbm" (is "_=?z_hbo")
  have z_Hbx_z_Hbm: "(Next=(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))) == ?z_hbm" (is "?z_hbx == _")
  by (unfold bEx_def)
  have z_Hbx: "?z_hbx" (is "_=?z_hby")
  by (unfold z_Hbx_z_Hbm, fact z_Hbm)
  show FALSE
  proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vu. (Next=zenon_Vu))" "(\<lambda>x. ((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))", OF z_Hbx])
   assume z_Hcj:"(?z_hby=TRUE)" (is "_=?z_hck")
   assume z_Hcl:"(Next=?z_hck)"
   have z_Hby: "?z_hby" (is "\\E x : ?z_hci(x)")
   by (rule zenon_eq_x_true_0 [of "?z_hby", OF z_Hcj])
   have z_Hbn: "Next"
   by (rule zenon_eq_x_true_0 [of "Next", OF z_Hcl])
   show FALSE
   proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hbv))" "Next" "(a_h4fd5f73954dc53af536c1c75068837a=vars)", OF z_He])
    assume z_Hcp:"(?z_hbu=?z_hck)"
    assume z_Hcq:"(?z_hck~=?z_hbv)"
    have z_Hcr: "(~?z_hbv)" (is "~(_|?z_hbj)")
    by (rule zenon_noteq_true_x_0 [of "?z_hbv", OF z_Hcq])
    have z_Hcs: "(~?z_hbo)"
    by (rule zenon_notor_0 [OF z_Hcr])
    have z_Hct_z_Hcs: "(~?z_hby) == (~?z_hbo)" (is "?z_hct == ?z_hcs")
    by (unfold bEx_def)
    have z_Hct: "?z_hct"
    by (unfold z_Hct_z_Hcs, fact z_Hcs)
    show FALSE
    by (rule notE [OF z_Hct z_Hby])
   next
    assume z_Hcu:"(?z_hbu=FALSE)" (is "_=?z_hcv")
    assume z_Hcw:"(?z_hcv~=?z_hbv)"
    have z_Hcx: "(~?z_hbu)" (is "~(_|?z_hbj)")
    by (rule zenon_eq_x_false_0 [of "?z_hbu", OF z_Hcu])
    have z_Hcy: "(~Next)"
    by (rule zenon_notor_0 [OF z_Hcx])
    show FALSE
    by (rule notE [OF z_Hcy z_Hbn])
   qed
  next
   assume z_Hcz:"(?z_hby=FALSE)" (is "_=?z_hcv")
   assume z_Hda:"(Next=?z_hcv)"
   have z_Hct: "(~?z_hby)" (is "~(\\E x : ?z_hci(x))")
   by (rule zenon_eq_x_false_0 [of "?z_hby", OF z_Hcz])
   have z_Hcy: "(~Next)"
   by (rule zenon_eq_x_false_0 [of "Next", OF z_Hda])
   show FALSE
   proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hbv))" "Next" "(a_h4fd5f73954dc53af536c1c75068837a=vars)", OF z_He])
    assume z_Hcp:"(?z_hbu=TRUE)" (is "_=?z_hck")
    assume z_Hcq:"(?z_hck~=?z_hbv)"
    have z_Hbu: "?z_hbu" (is "_|?z_hbj")
    by (rule zenon_eq_x_true_0 [of "?z_hbu", OF z_Hcp])
    have z_Hcr: "(~?z_hbv)"
    by (rule zenon_noteq_true_x_0 [of "?z_hbv", OF z_Hcq])
    have z_Hdb: "(a_h4fd5f73954dc53af536c1c75068837a~=vars)"
    by (rule zenon_notor_1 [OF z_Hcr])
    show FALSE
    proof (rule zenon_or [OF z_Hbu])
     assume z_Hbn:"Next"
     show FALSE
     by (rule notE [OF z_Hcy z_Hbn])
    next
     assume z_Hbj:"?z_hbj"
     show FALSE
     by (rule notE [OF z_Hdb z_Hbj])
    qed
   next
    assume z_Hcu:"(?z_hbu=?z_hcv)"
    assume z_Hcw:"(?z_hcv~=?z_hbv)"
    have z_Hcx: "(~?z_hbu)" (is "~(_|?z_hbj)")
    by (rule zenon_eq_x_false_0 [of "?z_hbu", OF z_Hcu])
    have z_Hdb: "(a_h4fd5f73954dc53af536c1c75068837a~=vars)"
    by (rule zenon_notor_1 [OF z_Hcx])
    show FALSE
    proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vha. (?z_hcv~=zenon_Vha))" "?z_hbo" "?z_hbj", OF z_Hcw])
     assume z_Hdf:"(?z_hbv=TRUE)" (is "_=?z_hck")
     assume z_Hdg:"(?z_hcv~=?z_hck)"
     have z_Hbv: "?z_hbv"
     by (rule zenon_eq_x_true_0 [of "?z_hbv", OF z_Hdf])
     show FALSE
     proof (rule zenon_or [OF z_Hbv])
      assume z_Hbo:"?z_hbo"
      have z_Hby_z_Hbo: "?z_hby == ?z_hbo" (is "_ == _")
      by (unfold bEx_def)
      have z_Hby: "?z_hby"
      by (unfold z_Hby_z_Hbo, fact z_Hbo)
      show FALSE
      by (rule notE [OF z_Hct z_Hby])
     next
      assume z_Hbj:"?z_hbj"
      show FALSE
      by (rule notE [OF z_Hdb z_Hbj])
     qed
    next
     assume z_Hdh:"(?z_hbv=?z_hcv)"
     assume z_Hdi:"(?z_hcv~=?z_hcv)"
     show FALSE
     by (rule zenon_eqsym [OF z_Hdh z_Hcw])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 948"; *} qed
lemma ob'890:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'121: "((((((((0)) \<in> (Int))) \<and> ((((arith_add ((b), ((minus (((Succ[0])))))))) \<in> (Int))))) \<and> (\<forall> x \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (((x) \<in> (Int))))))"
assumes v'122: "(\<forall> i \<in> (Int) : (\<forall> j \<in> (Int) : ((IsFiniteSet (((isa_peri_peri_a ((i), (j)))))))))"
assumes v'123: "(\<forall>S : (\<forall>T : ((((((IsFiniteSet ((T)))) \<and> (((S) \<subseteq> (T))))) \<Rightarrow> ((IsFiniteSet ((S))))))))"
shows "((IsFiniteSet ((subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))), %a_ca. (\<exists> a \<in> (Q) : ((~ ((DidNotVoteIn ((a), (a_ca))))))))))))"(is "PROP ?ob'890")
proof -
ML_command {* writeln "*** TLAPS ENTER 890"; *}
show "PROP ?ob'890"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_d45f81.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_d45f81.znn.out
;; obligation #890
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'121" (/\ (/\ (TLA.in 0 arith.Z) (TLA.in (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0))) arith.Z)) (TLA.bAll (arith.intrange 0
(arith.add b (arith.minus (TLA.fapply TLA.Succ 0)))) ((x) (TLA.in x
arith.Z))))
$hyp "v'122" (TLA.bAll arith.Z ((i) (TLA.bAll arith.Z ((j) (IsFiniteSet (arith.intrange i
j))))))
$hyp "v'123" (A. ((S) (A. ((T) (=> (/\ (IsFiniteSet T) (TLA.subseteq S T))
(IsFiniteSet S))))))
$goal (IsFiniteSet (TLA.subsetOf (arith.intrange 0 (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (TLA.bEx Q ((a) (-. (DidNotVoteIn a
a_ca)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hc:"(((0 \\in Int)&((b +  -.(1)) \\in Int))&bAll(isa'dotdot(0, (b +  -.(1))), (\<lambda>x. (x \\in Int))))" (is "?z_hg&?z_hp")
 using v'121 by blast
 have z_He:"(\\A S:(\\A T:((IsFiniteSet(T)&(S \\subseteq T))=>IsFiniteSet(S))))" (is "\\A x : ?z_hbc(x)")
 using v'123 by blast
 have z_Hd:"bAll(Int, (\<lambda>i. bAll(Int, (\<lambda>j. IsFiniteSet(isa'dotdot(i, j))))))" (is "?z_hd")
 using v'122 by blast
 have zenon_L1_: "(\\A T:((IsFiniteSet(T)&(subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))) \\subseteq T))=>IsFiniteSet(subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca))))))))) ==> IsFiniteSet(isa'dotdot(0, (b +  -.(1)))) ==> (~IsFiniteSet(subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))))) ==> FALSE" (is "?z_hbk ==> ?z_hby ==> ?z_hf ==> FALSE")
 proof -
  assume z_Hbk:"?z_hbk" (is "\\A x : ?z_hbz(x)")
  assume z_Hby:"?z_hby"
  assume z_Hf:"?z_hf" (is "~?z_hbx")
  have z_Hca: "?z_hbz(isa'dotdot(0, (b +  -.(1))))" (is "?z_hcb=>_")
  by (rule zenon_all_0 [of "?z_hbz" "isa'dotdot(0, (b +  -.(1)))", OF z_Hbk])
  show FALSE
  proof (rule zenon_imply [OF z_Hca])
   assume z_Hcc:"(~?z_hcb)" (is "~(_&?z_hcd)")
   show FALSE
   proof (rule zenon_notand [OF z_Hcc])
    assume z_Hce:"(~?z_hby)"
    show FALSE
    by (rule notE [OF z_Hce z_Hby])
   next
    assume z_Hcf:"(~?z_hcd)"
    have z_Hcg_z_Hcf: "(~bAll(subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))), (\<lambda>zenon_Vza. (zenon_Vza \\in isa'dotdot(0, (b +  -.(1))))))) == (~?z_hcd)" (is "?z_hcg == ?z_hcf")
    by (unfold subset_def)
    have z_Hcg: "?z_hcg" (is "~?z_hch")
    by (unfold z_Hcg_z_Hcf, fact z_Hcf)
    have z_Hcl_z_Hcg: "(~(\\A x:((x \\in subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))))=>(x \\in isa'dotdot(0, (b +  -.(1))))))) == ?z_hcg" (is "?z_hcl == _")
    by (unfold bAll_def)
    have z_Hcl: "?z_hcl" (is "~(\\A x : ?z_hcq(x))")
    by (unfold z_Hcl_z_Hcg, fact z_Hcg)
    have z_Hcr: "(\\E x:(~((x \\in subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))))=>(x \\in isa'dotdot(0, (b +  -.(1)))))))" (is "\\E x : ?z_hct(x)")
    by (rule zenon_notallex_0 [of "?z_hcq", OF z_Hcl])
    have z_Hcu: "?z_hct((CHOOSE x:(~((x \\in subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))))=>(x \\in isa'dotdot(0, (b +  -.(1))))))))" (is "~(?z_hcw=>?z_hcx)")
    by (rule zenon_ex_choose_0 [of "?z_hct", OF z_Hcr])
    have z_Hcw: "?z_hcw"
    by (rule zenon_notimply_0 [OF z_Hcu])
    have z_Hcy: "(~?z_hcx)"
    by (rule zenon_notimply_1 [OF z_Hcu])
    have z_Hcx: "?z_hcx"
    by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))))=>(x \\in isa'dotdot(0, (b +  -.(1)))))))" "isa'dotdot(0, (b +  -.(1)))" "(\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))", OF z_Hcw])
    show FALSE
    by (rule notE [OF z_Hcy z_Hcx])
   qed
  next
   assume z_Hbx:"?z_hbx"
   show FALSE
   by (rule notE [OF z_Hf z_Hbx])
  qed
 qed
 assume z_Hf:"(~IsFiniteSet(subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca))))))))" (is "~?z_hbx")
 have z_Hg: "?z_hg" (is "?z_hh&?z_hk")
 by (rule zenon_and_0 [OF z_Hc])
 have z_Hh: "?z_hh"
 by (rule zenon_and_0 [OF z_Hg])
 have z_Hk: "?z_hk"
 by (rule zenon_and_1 [OF z_Hg])
 have z_Hbk: "?z_hbc(subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca)))))))" (is "\\A x : ?z_hbz(x)")
 by (rule zenon_all_0 [of "?z_hbc" "subsetOf(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. bEx(Q, (\<lambda>a. (~DidNotVoteIn(a, a_ca))))))", OF z_He])
 have z_Hcz: "bAll(Int, (\<lambda>j. IsFiniteSet(isa'dotdot(0, j))))" (is "?z_hcz")
 by (rule zenon_all_in_0 [of "Int" "(\<lambda>i. bAll(Int, (\<lambda>j. IsFiniteSet(isa'dotdot(i, j)))))", OF z_Hd z_Hh])
 have z_Hdd_z_Hcz: "(\\A x:((x \\in Int)=>IsFiniteSet(isa'dotdot(0, x)))) == ?z_hcz" (is "?z_hdd == _")
 by (unfold bAll_def)
 have z_Hdd: "?z_hdd" (is "\\A x : ?z_hdh(x)")
 by (unfold z_Hdd_z_Hcz, fact z_Hcz)
 have z_Hdi: "?z_hdh((b +  -.(1)))" (is "_=>?z_hby")
 by (rule zenon_all_0 [of "?z_hdh" "(b +  -.(1))", OF z_Hdd])
 show FALSE
 proof (rule zenon_imply [OF z_Hdi])
  assume z_Hdj:"(~?z_hk)"
  show FALSE
  by (rule notE [OF z_Hdj z_Hk])
 next
  assume z_Hby:"?z_hby"
  show FALSE
  by (rule zenon_L1_ [OF z_Hbk z_Hby z_Hf])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 890"; *} qed
lemma ob'995:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes a
assumes a_in : "(a \<in> (Q))"
assumes v'122: "((((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))) & (((\<exists> self \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : (((BallotAction ((self), (a_ca)))) & (((((self) \<in> (Q))) \<Rightarrow> ((leq ((a_ca), (b))))))))) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))))"
assumes v'123: "(((fapply ((maxBal), (a))) = (b)))"
assumes v'124: "(((TypeOK) \<Rightarrow> (((Next) = (\<exists> self \<in> (Acceptor) : (\<exists> b_1 \<in> (Ballot) : ((BallotAction ((self), (b_1))))))))))"
shows "(((((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))))) = (((\<exists> self \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : ((BallotAction ((self), (a_ca)))))) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"(is "PROP ?ob'995")
proof -
ML_command {* writeln "*** TLAPS ENTER 995"; *}
show "PROP ?ob'995"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_af057e.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_af057e.znn.out
;; obligation #995
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "a_in" (TLA.in a Q)
$hyp "v'122" (/\ (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a) a_VInv4a)
(\/ (TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((a_ca) (/\ (BallotAction self
a_ca) (=> (TLA.in self Q) (arith.le a_ca b)))))))
(= a_h4fd5f73954dc53af536c1c75068837a
vars)))
$hyp "v'123" (= (TLA.fapply maxBal a) b)
$hyp "v'124" (=> TypeOK (= Next
(TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((b_1) (BallotAction self
b_1)))))))
$goal (= (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a vars))
(\/ (TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((a_ca) (BallotAction self
a_ca))))) (= a_h4fd5f73954dc53af536c1c75068837a
vars)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"((((TypeOK&a_VInv2a)&a_VInv3a)&a_VInv4a)&(bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>a_ca. (BallotAction(self, a_ca)&((self \\in Q)=>(a_ca <= b)))))))|(a_h4fd5f73954dc53af536c1c75068837a=vars)))" (is "?z_hh&?z_ho")
 using v'122 by blast
 have z_Hf:"(TypeOK=>(Next=bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b_1. BallotAction(self, b_1)))))))" (is "_=>?z_hbh")
 using v'124 by blast
 assume z_Hg:"((Next|(a_h4fd5f73954dc53af536c1c75068837a=vars))~=(bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b_1. BallotAction(self, b_1)))))|(a_h4fd5f73954dc53af536c1c75068837a=vars)))" (is "?z_hbp~=?z_hbq")
 have z_Hh: "?z_hh" (is "?z_hi&_")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hi: "?z_hi" (is "?z_hj&_")
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hj: "?z_hj"
 by (rule zenon_and_0 [OF z_Hi])
 have z_Hk: "TypeOK"
 by (rule zenon_and_0 [OF z_Hj])
 show FALSE
 proof (rule zenon_imply [OF z_Hf])
  assume z_Hbr:"(~TypeOK)"
  show FALSE
  by (rule notE [OF z_Hbr z_Hk])
 next
  assume z_Hbh:"?z_hbh" (is "_=?z_hbj")
  have z_Hbs_z_Hbh: "(Next=(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))) == ?z_hbh" (is "?z_hbs == _")
  by (unfold bEx_def)
  have z_Hbs: "?z_hbs" (is "_=?z_hbt")
  by (unfold z_Hbs_z_Hbh, fact z_Hbh)
  show FALSE
  proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vu. (Next=zenon_Vu))" "(\<lambda>x. ((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))", OF z_Hbs])
   assume z_Hce:"(?z_hbt=TRUE)" (is "_=?z_hcf")
   assume z_Hcg:"(Next=?z_hcf)"
   have z_Hbt: "?z_hbt" (is "\\E x : ?z_hcd(x)")
   by (rule zenon_eq_x_true_0 [of "?z_hbt", OF z_Hce])
   have z_Hbi: "Next"
   by (rule zenon_eq_x_true_0 [of "Next", OF z_Hcg])
   show FALSE
   proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hbq))" "Next" "(a_h4fd5f73954dc53af536c1c75068837a=vars)", OF z_Hg])
    assume z_Hck:"(?z_hbp=?z_hcf)"
    assume z_Hcl:"(?z_hcf~=?z_hbq)"
    have z_Hcm: "(~?z_hbq)" (is "~(_|?z_hbe)")
    by (rule zenon_noteq_true_x_0 [of "?z_hbq", OF z_Hcl])
    have z_Hcn: "(~?z_hbj)"
    by (rule zenon_notor_0 [OF z_Hcm])
    have z_Hco_z_Hcn: "(~?z_hbt) == (~?z_hbj)" (is "?z_hco == ?z_hcn")
    by (unfold bEx_def)
    have z_Hco: "?z_hco"
    by (unfold z_Hco_z_Hcn, fact z_Hcn)
    show FALSE
    by (rule notE [OF z_Hco z_Hbt])
   next
    assume z_Hcp:"(?z_hbp=FALSE)" (is "_=?z_hcq")
    assume z_Hcr:"(?z_hcq~=?z_hbq)"
    have z_Hcs: "(~?z_hbp)" (is "~(_|?z_hbe)")
    by (rule zenon_eq_x_false_0 [of "?z_hbp", OF z_Hcp])
    have z_Hct: "(~Next)"
    by (rule zenon_notor_0 [OF z_Hcs])
    show FALSE
    by (rule notE [OF z_Hct z_Hbi])
   qed
  next
   assume z_Hcu:"(?z_hbt=FALSE)" (is "_=?z_hcq")
   assume z_Hcv:"(Next=?z_hcq)"
   have z_Hco: "(~?z_hbt)" (is "~(\\E x : ?z_hcd(x))")
   by (rule zenon_eq_x_false_0 [of "?z_hbt", OF z_Hcu])
   have z_Hct: "(~Next)"
   by (rule zenon_eq_x_false_0 [of "Next", OF z_Hcv])
   show FALSE
   proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hbq))" "Next" "(a_h4fd5f73954dc53af536c1c75068837a=vars)", OF z_Hg])
    assume z_Hck:"(?z_hbp=TRUE)" (is "_=?z_hcf")
    assume z_Hcl:"(?z_hcf~=?z_hbq)"
    have z_Hbp: "?z_hbp" (is "_|?z_hbe")
    by (rule zenon_eq_x_true_0 [of "?z_hbp", OF z_Hck])
    have z_Hcm: "(~?z_hbq)"
    by (rule zenon_noteq_true_x_0 [of "?z_hbq", OF z_Hcl])
    have z_Hcw: "(a_h4fd5f73954dc53af536c1c75068837a~=vars)"
    by (rule zenon_notor_1 [OF z_Hcm])
    show FALSE
    proof (rule zenon_or [OF z_Hbp])
     assume z_Hbi:"Next"
     show FALSE
     by (rule notE [OF z_Hct z_Hbi])
    next
     assume z_Hbe:"?z_hbe"
     show FALSE
     by (rule notE [OF z_Hcw z_Hbe])
    qed
   next
    assume z_Hcp:"(?z_hbp=?z_hcq)"
    assume z_Hcr:"(?z_hcq~=?z_hbq)"
    have z_Hcs: "(~?z_hbp)" (is "~(_|?z_hbe)")
    by (rule zenon_eq_x_false_0 [of "?z_hbp", OF z_Hcp])
    have z_Hcw: "(a_h4fd5f73954dc53af536c1c75068837a~=vars)"
    by (rule zenon_notor_1 [OF z_Hcs])
    show FALSE
    proof (rule zenon_boolcase_or [of "(\<lambda>zenon_Vha. (?z_hcq~=zenon_Vha))" "?z_hbj" "?z_hbe", OF z_Hcr])
     assume z_Hda:"(?z_hbq=TRUE)" (is "_=?z_hcf")
     assume z_Hdb:"(?z_hcq~=?z_hcf)"
     have z_Hbq: "?z_hbq"
     by (rule zenon_eq_x_true_0 [of "?z_hbq", OF z_Hda])
     show FALSE
     proof (rule zenon_or [OF z_Hbq])
      assume z_Hbj:"?z_hbj"
      have z_Hbt_z_Hbj: "?z_hbt == ?z_hbj" (is "_ == _")
      by (unfold bEx_def)
      have z_Hbt: "?z_hbt"
      by (unfold z_Hbt_z_Hbj, fact z_Hbj)
      show FALSE
      by (rule notE [OF z_Hco z_Hbt])
     next
      assume z_Hbe:"?z_hbe"
      show FALSE
      by (rule notE [OF z_Hcw z_Hbe])
     qed
    next
     assume z_Hdc:"(?z_hbq=?z_hcq)"
     assume z_Hdd:"(?z_hcq~=?z_hcq)"
     show FALSE
     by (rule zenon_eqsym [OF z_Hdc z_Hcr])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 995"; *} qed
lemma ob'1016:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes a
assumes a_in : "(a \<in> (Q))"
fixes self
assumes self_in : "(self \<in> (Acceptor))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (Ballot))"
assumes v'128: "(((a) \<in> (Acceptor)))"
assumes v'138: "((greater ((a_ca), (b))))"
assumes v'139: "((~ ((greater ((a_ca), (b))))))"
shows "(((fapply (((a_maxBalhash_primea :: c)), (a))) = (b)))"(is "PROP ?ob'1016")
proof -
ML_command {* writeln "*** TLAPS ENTER 1016"; *}
show "PROP ?ob'1016"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_384b6b.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_384b6b.znn.out
;; obligation #1016
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "a_in" (TLA.in a Q)
$hyp "self_in" (TLA.in self Acceptor)
$hyp "a_ca_in" (TLA.in a_ca Ballot)
$hyp "v'128" (TLA.in a Acceptor)
$hyp "v'138" (arith.lt b a_ca)
$hyp "v'139" (-. (arith.lt b
a_ca))
$goal (= (TLA.fapply a_maxBalhash_primea a)
b)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(~(b < a_ca))" (is "~?z_hg")
 using v'139 by blast
 have z_Hg:"?z_hg"
 using v'138 by blast
 assume z_Hi:"((a_maxBalhash_primea[a])~=b)" (is "?z_hl~=_")
 show FALSE
 by (rule notE [OF z_Hh z_Hg])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1016"; *} qed
lemma ob'1083:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'128: "(((greater ((b), (fapply ((maxBal), (self)))))) & (((<<((votes)), (([(maxBal) EXCEPT ![(self)] = (b)]))>>) \<noteq> (<<(votes), (maxBal)>>))))"
assumes v'129: "(((([(maxBal) EXCEPT ![(self)] = (b)])) = ([(maxBal) EXCEPT ![(self)] = (b)])))"
assumes v'130: "((((votes)) = (votes)))"
shows "(\<exists>votesp : (\<exists>maxBalp : ((((greater ((b), (fapply ((maxBal), (self)))))) & (((maxBalp) = ([(maxBal) EXCEPT ![(self)] = (b)]))) & (((votesp) = (votes)))) & (((<<(votesp), (maxBalp)>>) \<noteq> (<<(votes), (maxBal)>>))))))"(is "PROP ?ob'1083")
proof -
ML_command {* writeln "*** TLAPS ENTER 1083"; *}
show "PROP ?ob'1083"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_f35099.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_f35099.znn.out
;; obligation #1083
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'128" (/\ (arith.lt (TLA.fapply maxBal self) b)
(-. (= (TLA.tuple votes (TLA.except maxBal self b)) (TLA.tuple votes
maxBal))))
$hyp "v'129" (= (TLA.except maxBal self b)
(TLA.except maxBal self b))
$hyp "v'130" (= votes
votes)
$goal (E. ((votesp) (E. ((maxBalp) (/\ (/\ (arith.lt (TLA.fapply maxBal self)
b) (= maxBalp (TLA.except maxBal self b)) (= votesp votes))
(-. (= (TLA.tuple votesp maxBalp) (TLA.tuple votes
maxBal))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(((maxBal[self]) < b)&(<<votes, except(maxBal, self, b)>>~=<<votes, maxBal>>))" (is "?z_hh&?z_hm")
 using v'128 by blast
 assume z_Hg:"(~(\\E votesp:(\\E maxBalp:((?z_hh&((maxBalp=except(maxBal, self, b))&(votesp=votes)))&(<<votesp, maxBalp>>~=<<votes, maxBal>>)))))" (is "~(\\E x : ?z_hbc(x))")
 have z_Hh: "?z_hh"
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hm: "?z_hm" (is "?z_hn~=?z_hq")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hbd: "~?z_hbc(votes)" (is "~(\\E x : ?z_hbe(x))")
 by (rule zenon_notex_0 [of "?z_hbc" "votes", OF z_Hg])
 have z_Hbf: "~?z_hbe(except(maxBal, self, b))" (is "~(?z_hbg&_)")
 by (rule zenon_notex_0 [of "?z_hbe" "except(maxBal, self, b)", OF z_Hbd])
 show FALSE
 proof (rule zenon_notand [OF z_Hbf])
  assume z_Hbh:"(~?z_hbg)" (is "~(_&?z_hbi)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbh])
   assume z_Hbj:"(~?z_hh)"
   show FALSE
   by (rule notE [OF z_Hbj z_Hh])
  next
   assume z_Hbk:"(~?z_hbi)" (is "~(?z_he&?z_hf)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbk])
    assume z_Hbl:"(except(maxBal, self, b)~=except(maxBal, self, b))" (is "?z_hp~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hbl])
   next
    assume z_Hbm:"(votes~=votes)"
    show FALSE
    by (rule zenon_noteq [OF z_Hbm])
   qed
  qed
 next
  assume z_Hbn:"(~?z_hm)" (is "~~?z_hbo")
  show FALSE
  by (rule notE [OF z_Hbn z_Hm])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1083"; *} qed
lemma ob'1178:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'142: "(((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))) \<Rightarrow> ((((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w))))))) \<in> (Acceptor))) & (((bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))) \<in> (Value))) & ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w))))))), (b), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w))))))))))))"
assumes v'143: "(((((((((((TypeOK) \<and> (\<forall> a \<in> (Acceptor) : (\<forall> b_1 \<in> (Ballot) : (\<forall> v \<in> (Value) : ((((VotedFor ((a), (b_1), (v)))) \<Rightarrow> ((SafeAt ((b_1), (v))))))))))) \<and> (a_VInv3a))) \<and> (a_VInv4a))) \<and> (\<forall> a \<in> (Q) : (((fapply ((maxBal), (a))) = (b)))))) \<and> ((~ (\<exists> v \<in> (Value) : ((VotedFor ((self), (b), (v)))))))))"
assumes v'144: "(\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w))))))"
shows "(((((cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))) \<in> (Value))) \<and> ((SafeAt ((b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))))))))"(is "PROP ?ob'1178")
proof -
ML_command {* writeln "*** TLAPS ENTER 1178"; *}
show "PROP ?ob'1178"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_d8dc90.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_d8dc90.znn.out
;; obligation #1178
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'142" (=> (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b w)))))
(/\ (TLA.in (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b w))))) Acceptor)
(TLA.in (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b w)))
Value) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b w))))) b
(TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))))))
$hyp "v'143" (/\ (/\ (/\ (/\ (/\ TypeOK
(TLA.bAll Acceptor ((a) (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((v) (=> (VotedFor a
b_1 v) (SafeAt b_1 v))))))))) a_VInv3a) a_VInv4a)
(TLA.bAll Q ((a) (= (TLA.fapply maxBal a) b))))
(-. (TLA.bEx Value ((v) (VotedFor self b
v)))))
$hyp "v'144" (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w)))))
$goal (/\ (TLA.in (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))) Value) (SafeAt b
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b
v))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(((((TypeOK&bAll(Acceptor, (\<lambda>a. bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v. (VotedFor(a, b_1, v)=>SafeAt(b_1, v)))))))))&a_VInv3a)&a_VInv4a)&bAll(Q, (\<lambda>a. ((maxBal[a])=b))))&(~bEx(Value, (\<lambda>v. VotedFor(self, b, v)))))" (is "?z_hh&?z_hbk")
 using v'143 by blast
 have z_Hf:"bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))" (is "?z_hf")
 using v'144 by blast
 have z_Hb:"(b \\in Ballot)" (is "?z_hb")
 using b_in by blast
 have z_Hd:"(?z_hf=>((bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))) \\in Acceptor)&((bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))) \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))))))" (is "_=>?z_hbx")
 using v'142 by blast
 assume z_Hg:"(~((cond(?z_hf, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))) \\in Value)&SafeAt(b, cond(?z_hf, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))))))" (is "~(?z_hch&?z_hcm)")
 have z_Hh: "?z_hh" (is "?z_hi&?z_hbd")
 by (rule zenon_and_0 [OF z_He])
 have z_Hi: "?z_hi" (is "?z_hj&_")
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hj: "?z_hj" (is "?z_hk&_")
 by (rule zenon_and_0 [OF z_Hi])
 have z_Hk: "?z_hk" (is "_&?z_hm")
 by (rule zenon_and_0 [OF z_Hj])
 have z_Hm: "?z_hm"
 by (rule zenon_and_1 [OF z_Hk])
 have z_Hcn_z_Hm: "(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>v. (VotedFor(x, b_1, v)=>SafeAt(b_1, v)))))))) == ?z_hm" (is "?z_hcn == _")
 by (unfold bAll_def)
 have z_Hcn: "?z_hcn" (is "\\A x : ?z_hcx(x)")
 by (unfold z_Hcn_z_Hm, fact z_Hm)
 have z_Hcy_z_Hf: "(\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))) == ?z_hf" (is "?z_hcy == _")
 by (unfold bEx_def)
 have z_Hcy: "?z_hcy" (is "\\E x : ?z_hde(x)")
 by (unfold z_Hcy_z_Hf, fact z_Hf)
 have z_Hdf: "?z_hde((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))))" (is "?z_hdh&?z_hdi")
 by (rule zenon_ex_choose_0 [of "?z_hde", OF z_Hcy])
 have z_Hdh: "?z_hdh"
 by (rule zenon_and_0 [OF z_Hdf])
 have z_Hdj: "((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))) \\in Acceptor)" (is "?z_hdj")
 by (rule zenon_in_setminus_0 [of "(CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w)))))" "Acceptor" "{self}", OF z_Hdh])
 show FALSE
 proof (rule zenon_imply [OF z_Hd])
  assume z_Hdk:"(~?z_hf)"
  show FALSE
  by (rule notE [OF z_Hdk z_Hf])
 next
  assume z_Hbx:"?z_hbx" (is "?z_hby&?z_hca")
  have z_Hca: "?z_hca" (is "?z_hcb&?z_hcf")
  by (rule zenon_and_1 [OF z_Hbx])
  have z_Hcb: "?z_hcb"
  by (rule zenon_and_0 [OF z_Hca])
  have z_Hcf: "?z_hcf"
  by (rule zenon_and_1 [OF z_Hca])
  show FALSE
  proof (rule zenon_notand [OF z_Hg])
   assume z_Hdl:"(~?z_hch)"
   show FALSE
   proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vbe. (~(zenon_Vbe \\in Value)))" "?z_hf" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hdl])
    assume z_Hf:"?z_hf"
    assume z_Hdq:"(~?z_hcb)"
    show FALSE
    by (rule notE [OF z_Hdq z_Hcb])
   next
    assume z_Hdk:"(~?z_hf)"
    assume z_Hdr:"(~(bChoice(Value, (\<lambda>v. SafeAt(b, v))) \\in Value))" (is "~?z_hds")
    show FALSE
    by (rule notE [OF z_Hdk z_Hf])
   qed
  next
   assume z_Hdt:"(~?z_hcm)"
   have z_Hdu_z_Hcb: "((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))) \\in Value) == ?z_hcb" (is "?z_hdu == _")
   by (unfold bChoose_def)
   have z_Hdu: "?z_hdu"
   by (unfold z_Hdu_z_Hcb, fact z_Hcb)
   have z_Hdz_z_Hcf: "VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))) == ?z_hcf" (is "?z_hdz == _")
   by (unfold bChoose_def)
   have z_Hdz: "?z_hdz"
   by (unfold z_Hdz_z_Hcf, fact z_Hcf)
   have z_Hea_z_Hdz: "VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, (CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))) == ?z_hdz" (is "?z_hea == _")
   by (unfold bChoose_def)
   have z_Hea: "?z_hea"
   by (unfold z_Hea_z_Hdz, fact z_Hdz)
   show FALSE
   proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vta. (~SafeAt(b, zenon_Vta)))" "?z_hf" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hdt])
    assume z_Hf:"?z_hf"
    assume z_Hef:"(~SafeAt(b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))))" (is "~?z_heg")
    have z_Heh_z_Hef: "(~SafeAt(b, (CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))))) == (~?z_heg)" (is "?z_heh == ?z_hef")
    by (unfold bChoose_def)
    have z_Heh: "?z_heh" (is "~?z_hei")
    by (unfold z_Heh_z_Hef, fact z_Hef)
    have z_Hej: "?z_hcx((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))))" (is "_=>?z_hek")
    by (rule zenon_all_0 [of "?z_hcx" "(CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w)))))", OF z_Hcn])
    show FALSE
    proof (rule zenon_imply [OF z_Hej])
     assume z_Hel:"(~?z_hdj)"
     show FALSE
     by (rule notE [OF z_Hel z_Hdj])
    next
     assume z_Hek:"?z_hek"
     have z_Hem_z_Hek: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>v. (VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), x, v)=>SafeAt(x, v)))))) == ?z_hek" (is "?z_hem == _")
     by (unfold bAll_def)
     have z_Hem: "?z_hem" (is "\\A x : ?z_heu(x)")
     by (unfold z_Hem_z_Hek, fact z_Hek)
     have z_Hev: "?z_heu(b)" (is "_=>?z_hew")
     by (rule zenon_all_0 [of "?z_heu" "b", OF z_Hem])
     show FALSE
     proof (rule zenon_imply [OF z_Hev])
      assume z_Hex:"(~?z_hb)"
      show FALSE
      by (rule notE [OF z_Hex z_Hb])
     next
      assume z_Hew:"?z_hew"
      have z_Hey_z_Hew: "(\\A x:((x \\in Value)=>(VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, x)=>SafeAt(b, x)))) == ?z_hew" (is "?z_hey == _")
      by (unfold bAll_def)
      have z_Hey: "?z_hey" (is "\\A x : ?z_hfd(x)")
      by (unfold z_Hey_z_Hew, fact z_Hew)
      have z_Hfe: "?z_hfd((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))))" (is "_=>?z_hff")
      by (rule zenon_all_0 [of "?z_hfd" "(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))", OF z_Hey])
      show FALSE
      proof (rule zenon_imply [OF z_Hfe])
       assume z_Hfg:"(~?z_hdu)"
       show FALSE
       by (rule notE [OF z_Hfg z_Hdu])
      next
       assume z_Hff:"?z_hff"
       show FALSE
       proof (rule zenon_imply [OF z_Hff])
        assume z_Hfh:"(~?z_hea)"
        show FALSE
        by (rule notE [OF z_Hfh z_Hea])
       next
        assume z_Hei:"?z_hei"
        show FALSE
        by (rule notE [OF z_Heh z_Hei])
       qed
      qed
     qed
    qed
   next
    assume z_Hdk:"(~?z_hf)"
    assume z_Hfi:"(~SafeAt(b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))))" (is "~?z_hfj")
    show FALSE
    by (rule notE [OF z_Hdk z_Hf])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1178"; *} qed
lemma ob'1175:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'143: "(((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))) \<Longrightarrow> (((((cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))) \<in> (Value))) \<and> ((SafeAt ((b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))))))))))"
assumes v'144: "((((~ (\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))))) \<Longrightarrow> (((((cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))) \<in> (Value))) \<and> ((SafeAt ((b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))))))))))"
shows "(((((cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))) \<in> (Value))) \<and> ((SafeAt ((b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))))))))"(is "PROP ?ob'1175")
proof -
ML_command {* writeln "*** TLAPS ENTER 1175"; *}
show "PROP ?ob'1175"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_2183e8.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_2183e8.znn.out
;; obligation #1175
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'143" (=> (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (/\ (TLA.in (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))) Value) (SafeAt b
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b
v)))))))
$hyp "v'144" (=> (-. (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w)))))) (/\ (TLA.in (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))) Value) (SafeAt b
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b
v)))))))
$goal (/\ (TLA.in (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))) Value) (SafeAt b
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b
v))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))=>((cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))) \\in Value)&SafeAt(b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))))))" (is "?z_hg=>?z_ht")
 using v'143 by blast
 have z_He:"((~?z_hg)=>?z_ht)" (is "?z_hbf=>_")
 using v'144 by blast
 assume z_Hf:"(~?z_ht)" (is "~(?z_hu&?z_hbe)")
 show FALSE
 proof (rule zenon_imply [OF z_Hd])
  assume z_Hbf:"?z_hbf"
  show FALSE
  proof (rule zenon_imply [OF z_He])
   assume z_Hbg:"(~?z_hbf)"
   show FALSE
   by (rule notE [OF z_Hbg z_Hbf])
  next
   assume z_Ht:"?z_ht"
   show FALSE
   by (rule notE [OF z_Hf z_Ht])
  qed
 next
  assume z_Ht:"?z_ht"
  show FALSE
  by (rule notE [OF z_Hf z_Ht])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1175"; *} qed
lemma ob'1174:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
shows "(((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))) \<Rightarrow> ((((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w))))))) \<in> (Acceptor))) & (((bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))) \<in> (Value))) & ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w))))))), (b), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w))))))))))))"(is "PROP ?ob'1174")
proof -
ML_command {* writeln "*** TLAPS ENTER 1174"; *}
show "PROP ?ob'1174"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_548f24.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_548f24.znn.out
;; obligation #1174
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$goal (=> (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b w)))))
(/\ (TLA.in (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b w))))) Acceptor)
(TLA.in (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b w)))
Value) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b w))))) b
(TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have zenon_L1_: "(~(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))) ==> ((CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, x))) \\in Value) ==> VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, (CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, x)))) ==> FALSE" (is "?z_he ==> ?z_hx ==> ?z_hbh ==> FALSE")
 proof -
  assume z_He:"?z_he" (is "~(\\E x : ?z_hbi(x))")
  assume z_Hx:"?z_hx"
  assume z_Hbh:"?z_hbh"
  have z_Hbj: "~?z_hbi((CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, x))))" (is "~(_&?z_hbk)")
  by (rule zenon_notex_0 [of "?z_hbi" "(CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, x)))", OF z_He])
  show FALSE
  proof (rule zenon_notand [OF z_Hbj])
   assume z_Hbl:"(~?z_hx)"
   show FALSE
   by (rule notE [OF z_Hbl z_Hx])
  next
   assume z_Hbm:"(~?z_hbk)"
   have z_Hbn_z_Hbm: "(~?z_hbh) == (~?z_hbk)" (is "?z_hbn == ?z_hbm")
   by (unfold bChoose_def)
   have z_Hbn: "?z_hbn"
   by (unfold z_Hbn_z_Hbm, fact z_Hbm)
   show FALSE
   by (rule notE [OF z_Hbn z_Hbh])
  qed
 qed
 assume z_Hd:"(~(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))=>((bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))) \\in Acceptor)&((bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))) \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))))))))" (is "~(?z_hbp=>?z_hbq)")
 have z_Hbp: "?z_hbp"
 by (rule zenon_notimply_0 [OF z_Hd])
 have z_Hby: "(~?z_hbq)" (is "~(?z_hbr&?z_hbs)")
 by (rule zenon_notimply_1 [OF z_Hd])
 have z_Hbz_z_Hbp: "(\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))) == ?z_hbp" (is "?z_hbz == _")
 by (unfold bEx_def)
 have z_Hbz: "?z_hbz" (is "\\E x : ?z_hca(x)")
 by (unfold z_Hbz_z_Hbp, fact z_Hbp)
 have z_Hcb: "?z_hca((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))))" (is "?z_hcc&?z_hcd")
 by (rule zenon_ex_choose_0 [of "?z_hca", OF z_Hbz])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hcd: "?z_hcd"
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hce: "((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))) \\in Acceptor)" (is "?z_hce")
 by (rule zenon_in_setminus_0 [of "(CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w)))))" "Acceptor" "{self}", OF z_Hcc])
 have z_Hcf_z_Hcd: "(\\E x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, x))) == ?z_hcd" (is "?z_hcf == _")
 by (unfold bEx_def)
 have z_Hcf: "?z_hcf" (is "\\E x : ?z_hcg(x)")
 by (unfold z_Hcf_z_Hcd, fact z_Hcd)
 have z_Hch: "?z_hcg((CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, x))))" (is "?z_hx&?z_hbh")
 by (rule zenon_ex_choose_0 [of "?z_hcg", OF z_Hcf])
 have z_Hx: "?z_hx"
 by (rule zenon_and_0 [OF z_Hch])
 have z_Hbh: "?z_hbh"
 by (rule zenon_and_1 [OF z_Hch])
 show FALSE
 proof (rule zenon_notand [OF z_Hby])
  assume z_Hci:"(~?z_hbr)"
  have z_Hcj_z_Hci: "(~?z_hce) == (~?z_hbr)" (is "?z_hcj == ?z_hci")
  by (unfold bChoose_def)
  have z_Hcj: "?z_hcj"
  by (unfold z_Hcj_z_Hci, fact z_Hci)
  show FALSE
  by (rule notE [OF z_Hcj z_Hce])
 next
  assume z_Hck:"(~?z_hbs)" (is "~(?z_hbt&?z_hbx)")
  show FALSE
  proof (rule zenon_notand [OF z_Hck])
   assume z_Hcl:"(~?z_hbt)"
   have z_Hcm_z_Hcl: "(~((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))) \\in Value)) == (~?z_hbt)" (is "?z_hcm == ?z_hcl")
   by (unfold bChoose_def)
   have z_Hcm: "?z_hcm" (is "~?z_hcn")
   by (unfold z_Hcm_z_Hcl, fact z_Hcl)
   show FALSE
   proof (rule zenon_em [of "(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))"])
    assume z_Hf:"(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))" (is "\\E x : ?z_hbi(x)")
    have z_Hcp: "?z_hbi((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))))" (is "_&?z_hcq")
    by (rule zenon_ex_choose_0 [of "?z_hbi", OF z_Hf])
    have z_Hcn: "?z_hcn"
    by (rule zenon_and_0 [OF z_Hcp])
    show FALSE
    by (rule notE [OF z_Hcm z_Hcn])
   next
    assume z_He:"(~(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))))" (is "~(\\E x : ?z_hbi(x))")
    show FALSE
    by (rule zenon_L1_ [OF z_He z_Hx z_Hbh])
   qed
  next
   assume z_Hcr:"(~?z_hbx)"
   have z_Hcs_z_Hcr: "(~VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))))) == (~?z_hbx)" (is "?z_hcs == ?z_hcr")
   by (unfold bChoose_def)
   have z_Hcs: "?z_hcs" (is "~?z_hct")
   by (unfold z_Hcs_z_Hcr, fact z_Hcr)
   have z_Hcu_z_Hcs: "(~VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w. VotedFor(x, b, w))))), b, (CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))))) == ?z_hcs" (is "?z_hcu == _")
   by (unfold bChoose_def)
   have z_Hcu: "?z_hcu" (is "~?z_hcv")
   by (unfold z_Hcu_z_Hcs, fact z_Hcs)
   show FALSE
   proof (rule zenon_em [of "(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))"])
    assume z_Hf:"(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))" (is "\\E x : ?z_hbi(x)")
    have z_Hcp: "?z_hbi((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))))" (is "?z_hcn&?z_hcq")
    by (rule zenon_ex_choose_0 [of "?z_hbi", OF z_Hf])
    have z_Hcq: "?z_hcq"
    by (rule zenon_and_1 [OF z_Hcp])
    have z_Hcv_z_Hcq: "?z_hcv == ?z_hcq" (is "_ == _")
    by (unfold bChoose_def)
    have z_Hcv: "?z_hcv"
    by (unfold z_Hcv_z_Hcq, fact z_Hcq)
    show FALSE
    by (rule notE [OF z_Hcu z_Hcv])
   next
    assume z_He:"(~(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))))" (is "~(\\E x : ?z_hbi(x))")
    show FALSE
    by (rule zenon_L1_ [OF z_He z_Hx z_Hbh])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1174"; *} qed
lemma ob'1168:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'148: "((leq ((fapply ((maxBal), (self))), (b))))"
assumes v'149: "((DidNotVoteIn ((self), (b))))"
assumes v'150: "((\<And> p :: c. p \<in> (((Acceptor) \\ ({(self)}))) \<Longrightarrow> (\<And> w :: c. w \<in> (Value) \<Longrightarrow> (((VotedFor ((p), (b), (w)))) \<Longrightarrow> (((w) = (cond((\<exists> p_1 \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w_1 \<in> (Value) : ((VotedFor ((p_1), (b), (w_1)))))), (bChoice((Value), %w_1. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p_1. (\<exists> w_2 \<in> (Value) : ((VotedFor ((p_1), (b), (w_2))))))), (b), (w_1)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))))))))"
assumes v'151: "((([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))]) \<noteq> (votes)))"
shows "(((leq ((fapply ((maxBal), (self))), (b)))) & ((DidNotVoteIn ((self), (b)))) & (\<forall> p \<in> (((Acceptor) \\ ({(self)}))) : (\<forall> w \<in> (Value) : ((((VotedFor ((p), (b), (w)))) \<Rightarrow> (((w) = (cond((\<exists> p_1 \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w_1 \<in> (Value) : ((VotedFor ((p_1), (b), (w_1)))))), (bChoice((Value), %w_1. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p_1. (\<exists> w_2 \<in> (Value) : ((VotedFor ((p_1), (b), (w_2))))))), (b), (w_1)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))))))))) & ((([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))]) \<noteq> (votes))))"(is "PROP ?ob'1168")
proof -
ML_command {* writeln "*** TLAPS ENTER 1168"; *}
show "PROP ?ob'1168"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_fd6768.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_fd6768.znn.out
;; obligation #1168
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'148" (arith.le (TLA.fapply maxBal self)
b)
$hyp "v'149" (DidNotVoteIn self
b)
$hyp "v'150" (TLA.bAll (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bAll Value ((w) (=> (VotedFor p b w) (= w
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_1) (VotedFor p_1 b
w_1))))) (TLA.bChoice Value ((w_1) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_2) (VotedFor p_1 b w_2))))) b
w_1))) (TLA.bChoice Value ((v) (SafeAt b
v))))))))))
$hyp "v'151" (-. (= (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v))))))))
votes))
$goal (/\ (arith.le (TLA.fapply maxBal self) b) (DidNotVoteIn self b)
(TLA.bAll (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bAll Value ((w) (=> (VotedFor p b w) (= w
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_1) (VotedFor p_1 b
w_1))))) (TLA.bChoice Value ((w_1) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_2) (VotedFor p_1 b w_2))))) b
w_1))) (TLA.bChoice Value ((v) (SafeAt b v))))))))))
(-. (= (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v))))))))
votes)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"((maxBal[self]) <= b)" (is "?z_hd")
 using v'148 by blast
 have z_He:"DidNotVoteIn(self, b)" (is "?z_he")
 using v'149 by blast
 have z_Hf:"bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))))))))" (is "?z_hf")
 using v'150 by blast
 have z_Hg:"(except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))~=votes)" (is "?z_hbo~=_")
 using v'151 by blast
 assume z_Hh:"(~(?z_hd&(?z_he&(?z_hf&(?z_hbo~=votes)))))" (is "~(_&?z_hbv)")
 show FALSE
 proof (rule zenon_notand [OF z_Hh])
  assume z_Hbx:"(~?z_hd)"
  show FALSE
  by (rule notE [OF z_Hbx z_Hd])
 next
  assume z_Hby:"(~?z_hbv)" (is "~(_&?z_hbw)")
  show FALSE
  proof (rule zenon_notand [OF z_Hby])
   assume z_Hbz:"(~?z_he)"
   show FALSE
   by (rule notE [OF z_Hbz z_He])
  next
   assume z_Hca:"(~?z_hbw)" (is "~(_&?z_hg)")
   show FALSE
   proof (rule zenon_notand [OF z_Hca])
    assume z_Hcb:"(~?z_hf)"
    show FALSE
    by (rule notE [OF z_Hcb z_Hf])
   next
    assume z_Hcc:"(~?z_hg)" (is "~~?z_hcd")
    show FALSE
    by (rule notE [OF z_Hcc z_Hg])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1168"; *} qed
lemma ob'1190:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'142: "(((leq ((fapply ((maxBal), (self))), (b)))) & ((DidNotVoteIn ((self), (b)))) & (\<forall> p \<in> (((Acceptor) \\ ({(self)}))) : (\<forall> w \<in> (Value) : ((((VotedFor ((p), (b), (w)))) \<Rightarrow> (((w) = (cond((\<exists> p_1 \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w_1 \<in> (Value) : ((VotedFor ((p_1), (b), (w_1)))))), (bChoice((Value), %w_1. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p_1. (\<exists> w_2 \<in> (Value) : ((VotedFor ((p_1), (b), (w_2))))))), (b), (w_1)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))))))))) & ((([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))]) \<noteq> (votes))))"
assumes v'143: "(((((cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))) \<in> (Value))) \<and> ((SafeAt ((b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))))))))"
shows "((\<exists> v \<in> (Value) : (((leq ((fapply ((maxBal), (self))), (b)))) & ((DidNotVoteIn ((self), (b)))) & (\<forall> p \<in> (((Acceptor) \\ ({(self)}))) : (\<forall> w \<in> (Value) : ((((VotedFor ((p), (b), (w)))) \<Rightarrow> (((w) = (v))))))) & ((SafeAt ((b), (v)))) & (((([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v_1. ((SafeAt ((b), (v_1))))))))>>)})))])) = ([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (v)>>)})))]))) & (((([(maxBal) EXCEPT ![(self)] = (b)])) = ([(maxBal) EXCEPT ![(self)] = (b)]))))) & (((<<(([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))])), (([(maxBal) EXCEPT ![(self)] = (b)]))>>) \<noteq> (<<(votes), (maxBal)>>))))"(is "PROP ?ob'1190")
proof -
ML_command {* writeln "*** TLAPS ENTER 1190"; *}
show "PROP ?ob'1190"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_fcab40.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_fcab40.znn.out
;; obligation #1190
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'142" (/\ (arith.le (TLA.fapply maxBal self) b) (DidNotVoteIn self b)
(TLA.bAll (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bAll Value ((w) (=> (VotedFor p b w) (= w
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_1) (VotedFor p_1 b
w_1))))) (TLA.bChoice Value ((w_1) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_2) (VotedFor p_1 b w_2))))) b
w_1))) (TLA.bChoice Value ((v) (SafeAt b v))))))))))
(-. (= (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v))))))))
votes)))
$hyp "v'143" (/\ (TLA.in (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))) Value) (SafeAt b
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b
v))))))
$goal (/\ (TLA.bEx Value ((v) (/\ (arith.le (TLA.fapply maxBal self) b)
(DidNotVoteIn self b) (TLA.bAll (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bAll Value ((w) (=> (VotedFor p b w) (= w v))))))
(SafeAt b v) (= (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v_1) (SafeAt b v_1))))))))
(TLA.except votes self (TLA.cup (TLA.fapply votes self) (TLA.set (TLA.tuple b
v))))) (= (TLA.except maxBal self b) (TLA.except maxBal self b)))))
(-. (= (TLA.tuple (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))))))) (TLA.except maxBal self b))
(TLA.tuple votes
maxBal))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(((maxBal[self]) <= b)&(DidNotVoteIn(self, b)&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))))))))&(except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))~=votes))))" (is "?z_hg&?z_hl")
 using v'142 by blast
 have z_He:"((cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))) \\in Value)&SafeAt(b, cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))))" (is "?z_hby&?z_hbz")
 using v'143 by blast
 have zenon_L1_: "((CHOOSE x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))))))=cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))) ==> bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))) ==> ((CHOOSE x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))))))~=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))) ==> FALSE" (is "?z_hca ==> ?z_hbc ==> ?z_hcv ==> FALSE")
 proof -
  assume z_Hca:"?z_hca" (is "?z_hcb=?z_hbb")
  assume z_Hbc:"?z_hbc"
  assume z_Hcv:"?z_hcv" (is "_~=?z_hcr")
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vjm. (?z_hcb=zenon_Vjm))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hca])
   assume z_Hbc:"?z_hbc"
   assume z_Hcz:"(?z_hcb=bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))))" (is "_=?z_hbj")
   have z_Hda_z_Hcz: "(?z_hcb=?z_hcr) == (?z_hcb=?z_hbj)" (is "?z_hda == ?z_hcz")
   by (unfold bChoose_def)
   have z_Hda: "?z_hda"
   by (unfold z_Hda_z_Hcz, fact z_Hcz)
   show FALSE
   by (rule notE [OF z_Hcv z_Hda])
  next
   assume z_Hdb:"(~?z_hbc)"
   assume z_Hdc:"(?z_hcb=bChoice(Value, (\<lambda>v. SafeAt(b, v))))" (is "_=?z_hbn")
   show FALSE
   by (rule notE [OF z_Hdb z_Hbc])
  qed
 qed
 have zenon_L2_: "bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))) ==> (\\A x:((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))))))))) ==> DidNotVoteIn(self, b) ==> ?z_hg ==> (~(\\E x:((x \\in Value)&(?z_hg&(DidNotVoteIn(self, b)&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&(except(maxBal, self, b)=except(maxBal, self, b)))))))))) ==> ?z_hbz ==> FALSE" (is "?z_hbc ==> ?z_hdd ==> ?z_hm ==> _ ==> ?z_hdi ==> _ ==> FALSE")
 proof -
  assume z_Hbc:"?z_hbc"
  assume z_Hdd:"?z_hdd" (is "\\A x : ?z_hee(x)")
  assume z_Hm:"?z_hm"
  assume z_Hg:"?z_hg"
  assume z_Hdi:"?z_hdi" (is "~(\\E x : ?z_hef(x))")
  assume z_Hbz:"?z_hbz"
  have z_Heg_z_Hbc: "(\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))) == ?z_hbc" (is "?z_heg == _")
  by (unfold bEx_def)
  have z_Heg: "?z_heg" (is "\\E x : ?z_hel(x)")
  by (unfold z_Heg_z_Hbc, fact z_Hbc)
  have z_Hem: "?z_hel((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))))" (is "?z_heo&?z_hep")
  by (rule zenon_ex_choose_0 [of "?z_hel", OF z_Heg])
  have z_Hep: "?z_hep"
  by (rule zenon_and_1 [OF z_Hem])
  have z_Heq_z_Hep: "(\\E x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x))) == ?z_hep" (is "?z_heq == _")
  by (unfold bEx_def)
  have z_Heq: "?z_heq" (is "\\E x : ?z_het(x)")
  by (unfold z_Heq_z_Hep, fact z_Hep)
  have z_Heu: "?z_het((CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x))))" (is "?z_hew&?z_hex")
  by (rule zenon_ex_choose_0 [of "?z_het", OF z_Heq])
  have z_Hew: "?z_hew"
  by (rule zenon_and_0 [OF z_Heu])
  have z_Hex: "?z_hex"
  by (rule zenon_and_1 [OF z_Heu])
  show FALSE
  proof (rule zenon_em [of "(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))"])
   assume z_Hey:"(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))" (is "\\E x : ?z_hez(x)")
   have z_Hfa: "?z_hez((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))" (is "?z_hfb&?z_hfc")
   by (rule zenon_ex_choose_0 [of "?z_hez", OF z_Hey])
   have z_Hfb: "?z_hfb"
   by (rule zenon_and_0 [OF z_Hfa])
   show FALSE
   proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vu. SafeAt(b, zenon_Vu))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hbz])
    assume z_Hbc:"?z_hbc"
    assume z_Hfg:"SafeAt(b, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))))" (is "?z_hfg")
    have z_Hfh_z_Hfg: "SafeAt(b, (CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))) == ?z_hfg" (is "?z_hfh == _")
    by (unfold bChoose_def)
    have z_Hfh: "?z_hfh"
    by (unfold z_Hfh_z_Hfg, fact z_Hfg)
    have z_Hfi: "~?z_hef((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))" (is "~(_&?z_hfj)")
    by (rule zenon_notex_0 [of "?z_hef" "(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))", OF z_Hdi])
    show FALSE
    proof (rule zenon_notand [OF z_Hfi])
     assume z_Hfk:"(~?z_hfb)"
     show FALSE
     by (rule notE [OF z_Hfk z_Hfb])
    next
     assume z_Hfl:"(~?z_hfj)" (is "~(_&?z_hfm)")
     show FALSE
     proof (rule zenon_notand [OF z_Hfl])
      assume z_Hfn:"(~?z_hg)"
      show FALSE
      by (rule notE [OF z_Hfn z_Hg])
     next
      assume z_Hfo:"(~?z_hfm)" (is "~(_&?z_hfp)")
      show FALSE
      proof (rule zenon_notand [OF z_Hfo])
       assume z_Hfq:"(~?z_hm)"
       show FALSE
       by (rule notE [OF z_Hfq z_Hm])
      next
       assume z_Hfr:"(~?z_hfp)" (is "~(?z_hfs&?z_hft)")
       show FALSE
       proof (rule zenon_notand [OF z_Hfr])
        assume z_Hfu:"(~?z_hfs)"
        have z_Hfv_z_Hfu: "(~(\\A x:((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))) == (~?z_hfs)" (is "?z_hfv == ?z_hfu")
        by (unfold bAll_def)
        have z_Hfv: "?z_hfv" (is "~(\\A x : ?z_hfx(x))")
        by (unfold z_Hfv_z_Hfu, fact z_Hfu)
        have z_Hfy: "(\\E x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))))))))" (is "\\E x : ?z_hfz(x)")
        by (rule zenon_notallex_0 [of "?z_hfx", OF z_Hfv])
        have z_Hga: "?z_hfz((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))))" (is "~(?z_hgb=>?z_hgc)")
        by (rule zenon_ex_choose_0 [of "?z_hfz", OF z_Hfy])
        have z_Hgb: "?z_hgb"
        by (rule zenon_notimply_0 [OF z_Hga])
        have z_Hgd: "(~?z_hgc)"
        by (rule zenon_notimply_1 [OF z_Hga])
        have z_Hge_z_Hgd: "(~(\\A x:((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))) == (~?z_hgc)" (is "?z_hge == ?z_hgd")
        by (unfold bAll_def)
        have z_Hge: "?z_hge" (is "~(\\A x : ?z_hgg(x))")
        by (unfold z_Hge_z_Hgd, fact z_Hgd)
        have z_Hgh: "(\\E x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))))))" (is "\\E x : ?z_hgi(x)")
        by (rule zenon_notallex_0 [of "?z_hgg", OF z_Hge])
        have z_Hgj: "?z_hgi((CHOOSE x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))" (is "~(?z_hgk=>?z_hgl)")
        by (rule zenon_ex_choose_0 [of "?z_hgi", OF z_Hgh])
        have z_Hgk: "?z_hgk"
        by (rule zenon_notimply_0 [OF z_Hgj])
        have z_Hgm: "(~?z_hgl)" (is "~(?z_hgn=>?z_hda)")
        by (rule zenon_notimply_1 [OF z_Hgj])
        have z_Hgn: "?z_hgn"
        by (rule zenon_notimply_0 [OF z_Hgm])
        have z_Hcv: "((CHOOSE x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))))))~=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))" (is "?z_hcb~=?z_hcr")
        by (rule zenon_notimply_1 [OF z_Hgm])
        have z_Hgo: "?z_hee((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=?z_hcr))))))))" (is "_=>?z_hgp")
        by (rule zenon_all_0 [of "?z_hee" "(CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=?z_hcr)))))))", OF z_Hdd])
        show FALSE
        proof (rule zenon_imply [OF z_Hgo])
         assume z_Hgq:"(~?z_hgb)"
         show FALSE
         by (rule notE [OF z_Hgq z_Hgb])
        next
         assume z_Hgp:"?z_hgp"
         have z_Hgr_z_Hgp: "(\\A x:((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=?z_hcr))))))), b, x)=>(x=cond(?z_hbc, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))))))) == ?z_hgp" (is "?z_hgr == _")
         by (unfold bAll_def)
         have z_Hgr: "?z_hgr" (is "\\A x : ?z_hgv(x)")
         by (unfold z_Hgr_z_Hgp, fact z_Hgp)
         have z_Hgw: "?z_hgv(?z_hcb)" (is "_=>?z_hgx")
         by (rule zenon_all_0 [of "?z_hgv" "?z_hcb", OF z_Hgr])
         show FALSE
         proof (rule zenon_imply [OF z_Hgw])
          assume z_Hgy:"(~?z_hgk)"
          show FALSE
          by (rule notE [OF z_Hgy z_Hgk])
         next
          assume z_Hgx:"?z_hgx" (is "_=>?z_hca")
          show FALSE
          proof (rule zenon_imply [OF z_Hgx])
           assume z_Hgz:"(~?z_hgn)"
           show FALSE
           by (rule notE [OF z_Hgz z_Hgn])
          next
           assume z_Hca:"?z_hca" (is "_=?z_hbb")
           show FALSE
           by (rule zenon_L1_ [OF z_Hca z_Hbc z_Hcv])
          qed
         qed
        qed
       next
        assume z_Hha:"(~?z_hft)" (is "~(_&?z_hhb)")
        show FALSE
        proof (rule zenon_notand [OF z_Hha])
         assume z_Hhc:"(~?z_hfh)"
         show FALSE
         by (rule notE [OF z_Hhc z_Hfh])
        next
         assume z_Hhd:"(~?z_hhb)" (is "~(?z_hhe&?z_hec)")
         show FALSE
         proof (rule zenon_notand [OF z_Hhd])
          assume z_Hhf:"(except(votes, self, ((votes[self]) \\cup {<<b, cond(?z_hbc, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))~=except(votes, self, ((votes[self]) \\cup {<<b, (CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))>>})))" (is "?z_hbs~=?z_hhg")
          show FALSE
          proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vym. (except(votes, self, ((votes[self]) \\cup {<<b, zenon_Vym>>}))~=?z_hhg))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hhf])
           assume z_Hbc:"?z_hbc"
           assume z_Hhr:"(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))>>}))~=?z_hhg)" (is "?z_hhs~=_")
           have z_Hhw_z_Hhr: "(?z_hhg~=?z_hhg) == (?z_hhs~=?z_hhg)" (is "?z_hhw == ?z_hhr")
           by (unfold bChoose_def)
           have z_Hhw: "?z_hhw"
           by (unfold z_Hhw_z_Hhr, fact z_Hhr)
           show FALSE
           by (rule zenon_noteq [OF z_Hhw])
          next
           assume z_Hdb:"(~?z_hbc)"
           assume z_Hhx:"(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))>>}))~=?z_hhg)" (is "?z_hhy~=_")
           show FALSE
           by (rule notE [OF z_Hdb z_Hbc])
          qed
         next
          assume z_Hic:"(except(maxBal, self, b)~=except(maxBal, self, b))" (is "?z_hed~=_")
          show FALSE
          by (rule zenon_noteq [OF z_Hic])
         qed
        qed
       qed
      qed
     qed
    qed
   next
    assume z_Hdb:"(~?z_hbc)"
    assume z_Hid:"SafeAt(b, bChoice(Value, (\<lambda>v. SafeAt(b, v))))" (is "?z_hid")
    show FALSE
    by (rule notE [OF z_Hdb z_Hbc])
   qed
  next
   assume z_Hie:"(~(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))" (is "~(\\E x : ?z_hez(x))")
   have z_Hif: "~?z_hez((CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x))))" (is "~(_&?z_hig)")
   by (rule zenon_notex_0 [of "?z_hez" "(CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x)))", OF z_Hie])
   show FALSE
   proof (rule zenon_notand [OF z_Hif])
    assume z_Hih:"(~?z_hew)"
    show FALSE
    by (rule notE [OF z_Hih z_Hew])
   next
    assume z_Hii:"(~?z_hig)"
    have z_Hij_z_Hii: "(~?z_hex) == (~?z_hig)" (is "?z_hij == ?z_hii")
    by (unfold bChoose_def)
    have z_Hij: "?z_hij"
    by (unfold z_Hij_z_Hii, fact z_Hii)
    show FALSE
    by (rule notE [OF z_Hij z_Hex])
   qed
  qed
 qed
 have zenon_L3_: "((CHOOSE x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&SafeAt(b, x))))))))=cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))) ==> ((CHOOSE x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&SafeAt(b, x))))))))~=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))) ==> (~bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1)))))) ==> FALSE" (is "?z_hik ==> ?z_hja ==> ?z_hdb ==> FALSE")
 proof -
  assume z_Hik:"?z_hik" (is "?z_hil=?z_hbb")
  assume z_Hja:"?z_hja" (is "_~=?z_hix")
  assume z_Hdb:"?z_hdb" (is "~?z_hbc")
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vrg. (?z_hil=zenon_Vrg))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hik])
   assume z_Hbc:"?z_hbc"
   assume z_Hje:"(?z_hil=bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))))" (is "_=?z_hbj")
   show FALSE
   by (rule notE [OF z_Hdb z_Hbc])
  next
   assume z_Hdb:"?z_hdb"
   assume z_Hjf:"(?z_hil=bChoice(Value, (\<lambda>v. SafeAt(b, v))))" (is "_=?z_hbn")
   have z_Hjg_z_Hjf: "(?z_hil=?z_hix) == (?z_hil=?z_hbn)" (is "?z_hjg == ?z_hjf")
   by (unfold bChoose_def)
   have z_Hjg: "?z_hjg"
   by (unfold z_Hjg_z_Hjf, fact z_Hjf)
   show FALSE
   by (rule notE [OF z_Hja z_Hjg])
  qed
 qed
 have zenon_L4_: "?z_hbz ==> ?z_hby ==> (~bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1)))))) ==> (\\A x:((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))))))))) ==> DidNotVoteIn(self, b) ==> ?z_hg ==> (~(\\E x:((x \\in Value)&(?z_hg&(DidNotVoteIn(self, b)&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&(except(maxBal, self, b)=except(maxBal, self, b)))))))))) ==> FALSE" (is "_ ==> _ ==> ?z_hdb ==> ?z_hdd ==> ?z_hm ==> _ ==> ?z_hdi ==> FALSE")
 proof -
  assume z_Hbz:"?z_hbz"
  assume z_Hby:"?z_hby"
  assume z_Hdb:"?z_hdb" (is "~?z_hbc")
  assume z_Hdd:"?z_hdd" (is "\\A x : ?z_hee(x)")
  assume z_Hm:"?z_hm"
  assume z_Hg:"?z_hg"
  assume z_Hdi:"?z_hdi" (is "~(\\E x : ?z_hef(x))")
  show FALSE
  proof (rule zenon_em [of "(\\E x:((x \\in Value)&SafeAt(b, x)))"])
   assume z_Hjh:"(\\E x:((x \\in Value)&SafeAt(b, x)))" (is "\\E x : ?z_hji(x)")
   have z_Hjj: "?z_hji((CHOOSE x:((x \\in Value)&SafeAt(b, x))))" (is "?z_hjk&?z_hjl")
   by (rule zenon_ex_choose_0 [of "?z_hji", OF z_Hjh])
   have z_Hjk: "?z_hjk"
   by (rule zenon_and_0 [OF z_Hjj])
   have z_Hjl: "?z_hjl"
   by (rule zenon_and_1 [OF z_Hjj])
   have z_Hjm: "~?z_hef((CHOOSE x:((x \\in Value)&SafeAt(b, x))))" (is "~(_&?z_hjn)")
   by (rule zenon_notex_0 [of "?z_hef" "(CHOOSE x:((x \\in Value)&SafeAt(b, x)))", OF z_Hdi])
   show FALSE
   proof (rule zenon_notand [OF z_Hjm])
    assume z_Hjo:"(~?z_hjk)"
    show FALSE
    by (rule notE [OF z_Hjo z_Hjk])
   next
    assume z_Hjp:"(~?z_hjn)" (is "~(_&?z_hjq)")
    show FALSE
    proof (rule zenon_notand [OF z_Hjp])
     assume z_Hfn:"(~?z_hg)"
     show FALSE
     by (rule notE [OF z_Hfn z_Hg])
    next
     assume z_Hjr:"(~?z_hjq)" (is "~(_&?z_hjs)")
     show FALSE
     proof (rule zenon_notand [OF z_Hjr])
      assume z_Hfq:"(~?z_hm)"
      show FALSE
      by (rule notE [OF z_Hfq z_Hm])
     next
      assume z_Hjt:"(~?z_hjs)" (is "~(?z_hju&?z_hjv)")
      show FALSE
      proof (rule zenon_notand [OF z_Hjt])
       assume z_Hjw:"(~?z_hju)"
       have z_Hjx_z_Hjw: "(~(\\A x:((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))) == (~?z_hju)" (is "?z_hjx == ?z_hjw")
       by (unfold bAll_def)
       have z_Hjx: "?z_hjx" (is "~(\\A x : ?z_hjz(x))")
       by (unfold z_Hjx_z_Hjw, fact z_Hjw)
       have z_Hka: "(\\E x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x))))))))))" (is "\\E x : ?z_hkb(x)")
       by (rule zenon_notallex_0 [of "?z_hjz", OF z_Hjx])
       have z_Hkc: "?z_hkb((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))))" (is "~(?z_hkd=>?z_hke)")
       by (rule zenon_ex_choose_0 [of "?z_hkb", OF z_Hka])
       have z_Hkd: "?z_hkd"
       by (rule zenon_notimply_0 [OF z_Hkc])
       have z_Hkf: "(~?z_hke)"
       by (rule zenon_notimply_1 [OF z_Hkc])
       have z_Hkg_z_Hkf: "(~(\\A x:((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))) == (~?z_hke)" (is "?z_hkg == ?z_hkf")
       by (unfold bAll_def)
       have z_Hkg: "?z_hkg" (is "~(\\A x : ?z_hki(x))")
       by (unfold z_Hkg_z_Hkf, fact z_Hkf)
       have z_Hkj: "(\\E x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&SafeAt(b, x))))))))" (is "\\E x : ?z_hkk(x)")
       by (rule zenon_notallex_0 [of "?z_hki", OF z_Hkg])
       have z_Hkl: "?z_hkk((CHOOSE x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))" (is "~(?z_hkm=>?z_hkn)")
       by (rule zenon_ex_choose_0 [of "?z_hkk", OF z_Hkj])
       have z_Hkm: "?z_hkm"
       by (rule zenon_notimply_0 [OF z_Hkl])
       have z_Hko: "(~?z_hkn)" (is "~(?z_hkp=>?z_hjg)")
       by (rule zenon_notimply_1 [OF z_Hkl])
       have z_Hkp: "?z_hkp"
       by (rule zenon_notimply_0 [OF z_Hko])
       have z_Hja: "((CHOOSE x:(~((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=(CHOOSE x:((x \\in Value)&SafeAt(b, x)))))))))), b, x)=>(x=(CHOOSE x:((x \\in Value)&SafeAt(b, x))))))))~=(CHOOSE x:((x \\in Value)&SafeAt(b, x))))" (is "?z_hil~=?z_hix")
       by (rule zenon_notimply_1 [OF z_Hko])
       have z_Hkq: "?z_hee((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=?z_hix))))))))" (is "_=>?z_hkr")
       by (rule zenon_all_0 [of "?z_hee" "(CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=?z_hix)))))))", OF z_Hdd])
       show FALSE
       proof (rule zenon_imply [OF z_Hkq])
        assume z_Hks:"(~?z_hkd)"
        show FALSE
        by (rule notE [OF z_Hks z_Hkd])
       next
        assume z_Hkr:"?z_hkr"
        have z_Hkt_z_Hkr: "(\\A x:((x \\in Value)=>(VotedFor((CHOOSE x:(~((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=?z_hix))))))), b, x)=>(x=cond(?z_hbc, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))))))) == ?z_hkr" (is "?z_hkt == _")
        by (unfold bAll_def)
        have z_Hkt: "?z_hkt" (is "\\A x : ?z_hkw(x)")
        by (unfold z_Hkt_z_Hkr, fact z_Hkr)
        have z_Hkx: "?z_hkw(?z_hil)" (is "_=>?z_hky")
        by (rule zenon_all_0 [of "?z_hkw" "?z_hil", OF z_Hkt])
        show FALSE
        proof (rule zenon_imply [OF z_Hkx])
         assume z_Hkz:"(~?z_hkm)"
         show FALSE
         by (rule notE [OF z_Hkz z_Hkm])
        next
         assume z_Hky:"?z_hky" (is "_=>?z_hik")
         show FALSE
         proof (rule zenon_imply [OF z_Hky])
          assume z_Hla:"(~?z_hkp)"
          show FALSE
          by (rule notE [OF z_Hla z_Hkp])
         next
          assume z_Hik:"?z_hik" (is "_=?z_hbb")
          show FALSE
          by (rule zenon_L3_ [OF z_Hik z_Hja z_Hdb])
         qed
        qed
       qed
      next
       assume z_Hlb:"(~?z_hjv)" (is "~(_&?z_hlc)")
       show FALSE
       proof (rule zenon_notand [OF z_Hlb])
        assume z_Hld:"(~?z_hjl)"
        show FALSE
        by (rule notE [OF z_Hld z_Hjl])
       next
        assume z_Hle:"(~?z_hlc)" (is "~(?z_hlf&?z_hec)")
        show FALSE
        proof (rule zenon_notand [OF z_Hle])
         assume z_Hlg:"(except(votes, self, ((votes[self]) \\cup {<<b, cond(?z_hbc, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))~=except(votes, self, ((votes[self]) \\cup {<<b, (CHOOSE x:((x \\in Value)&SafeAt(b, x)))>>})))" (is "?z_hbs~=?z_hlh")
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vnh. (except(votes, self, ((votes[self]) \\cup {<<b, zenon_Vnh>>}))~=?z_hlh))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hlg])
          assume z_Hbc:"?z_hbc"
          assume z_Hls:"(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))>>}))~=?z_hlh)" (is "?z_hhs~=_")
          show FALSE
          by (rule notE [OF z_Hdb z_Hbc])
         next
          assume z_Hdb:"?z_hdb"
          assume z_Hlt:"(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))>>}))~=?z_hlh)" (is "?z_hhy~=_")
          have z_Hlu_z_Hlt: "(?z_hlh~=?z_hlh) == (?z_hhy~=?z_hlh)" (is "?z_hlu == ?z_hlt")
          by (unfold bChoose_def)
          have z_Hlu: "?z_hlu"
          by (unfold z_Hlu_z_Hlt, fact z_Hlt)
          show FALSE
          by (rule zenon_noteq [OF z_Hlu])
         qed
        next
         assume z_Hic:"(except(maxBal, self, b)~=except(maxBal, self, b))" (is "?z_hed~=_")
         show FALSE
         by (rule zenon_noteq [OF z_Hic])
        qed
       qed
      qed
     qed
    qed
   qed
  next
   assume z_Hlv:"(~(\\E x:((x \\in Value)&SafeAt(b, x))))" (is "~(\\E x : ?z_hji(x))")
   show FALSE
   proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vv. (zenon_Vv \\in Value))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hby])
    assume z_Hbc:"?z_hbc"
    assume z_Hlz:"(bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))) \\in Value)" (is "?z_hlz")
    show FALSE
    by (rule notE [OF z_Hdb z_Hbc])
   next
    assume z_Hdb:"?z_hdb"
    assume z_Hma:"(bChoice(Value, (\<lambda>v. SafeAt(b, v))) \\in Value)" (is "?z_hma")
    have z_Hjk_z_Hma: "((CHOOSE x:((x \\in Value)&SafeAt(b, x))) \\in Value) == ?z_hma" (is "?z_hjk == _")
    by (unfold bChoose_def)
    have z_Hjk: "?z_hjk"
    by (unfold z_Hjk_z_Hma, fact z_Hma)
    show FALSE
    proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vu. SafeAt(b, zenon_Vu))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hbz])
     assume z_Hbc:"?z_hbc"
     assume z_Hfg:"SafeAt(b, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))))" (is "?z_hfg")
     show FALSE
     by (rule notE [OF z_Hdb z_Hbc])
    next
     assume z_Hdb:"?z_hdb"
     assume z_Hid:"SafeAt(b, bChoice(Value, (\<lambda>v. SafeAt(b, v))))" (is "?z_hid")
     have z_Hjl_z_Hid: "SafeAt(b, (CHOOSE x:((x \\in Value)&SafeAt(b, x)))) == ?z_hid" (is "?z_hjl == _")
     by (unfold bChoose_def)
     have z_Hjl: "?z_hjl"
     by (unfold z_Hjl_z_Hid, fact z_Hid)
     have z_Hmb: "~?z_hji((CHOOSE x:((x \\in Value)&SafeAt(b, x))))"
     by (rule zenon_notex_0 [of "?z_hji" "(CHOOSE x:((x \\in Value)&SafeAt(b, x)))", OF z_Hlv])
     show FALSE
     proof (rule zenon_notand [OF z_Hmb])
      assume z_Hjo:"(~?z_hjk)"
      show FALSE
      by (rule notE [OF z_Hjo z_Hjk])
     next
      assume z_Hld:"(~?z_hjl)"
      show FALSE
      by (rule notE [OF z_Hld z_Hjl])
     qed
    qed
   qed
  qed
 qed
 assume z_Hf:"(~(bEx(Value, (\<lambda>v. (?z_hg&(DidNotVoteIn(self, b)&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=v))))))&(SafeAt(b, v)&((except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))=except(votes, self, ((votes[self]) \\cup {<<b, v>>})))&(except(maxBal, self, b)=except(maxBal, self, b)))))))))&(<<except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>})), except(maxBal, self, b)>>~=<<votes, maxBal>>)))" (is "~(?z_hmd&?z_hmv)")
 have z_Hg: "?z_hg"
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hl: "?z_hl" (is "?z_hm&?z_hn")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hm: "?z_hm"
 by (rule zenon_and_0 [OF z_Hl])
 have z_Hn: "?z_hn" (is "?z_ho&?z_hbr")
 by (rule zenon_and_1 [OF z_Hl])
 have z_Ho: "?z_ho"
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hbr: "?z_hbr" (is "?z_hbs~=_")
 by (rule zenon_and_1 [OF z_Hn])
 have z_Hdd_z_Ho: "(\\A x:((x \\in (Acceptor \\ {self}))=>bAll(Value, (\<lambda>w. (VotedFor(x, b, w)=>(w=cond(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))))))))) == ?z_ho" (is "?z_hdd == _")
 by (unfold bAll_def)
 have z_Hdd: "?z_hdd" (is "\\A x : ?z_hee(x)")
 by (unfold z_Hdd_z_Ho, fact z_Ho)
 have z_Hby: "?z_hby"
 by (rule zenon_and_0 [OF z_He])
 have z_Hbz: "?z_hbz"
 by (rule zenon_and_1 [OF z_He])
 show FALSE
 proof (rule zenon_notand [OF z_Hf])
  assume z_Hmy:"(~?z_hmd)"
  have z_Hdi_z_Hmy: "(~(\\E x:((x \\in Value)&(?z_hg&(?z_hm&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((?z_hbs=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&(except(maxBal, self, b)=except(maxBal, self, b)))))))))) == (~?z_hmd)" (is "?z_hdi == ?z_hmy")
  by (unfold bEx_def)
  have z_Hdi: "?z_hdi" (is "~(\\E x : ?z_hef(x))")
  by (unfold z_Hdi_z_Hmy, fact z_Hmy)
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vv. (zenon_Vv \\in Value))" "bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1)))))" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hby])
   assume z_Hbc:"bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1)))))" (is "?z_hbc")
   assume z_Hlz:"(bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))) \\in Value)" (is "?z_hlz")
   show FALSE
   by (rule zenon_L2_ [OF z_Hbc z_Hdd z_Hm z_Hg z_Hdi z_Hbz])
  next
   assume z_Hdb:"(~bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))))" (is "~?z_hbc")
   assume z_Hma:"(bChoice(Value, (\<lambda>v. SafeAt(b, v))) \\in Value)" (is "?z_hma")
   show FALSE
   by (rule zenon_L4_ [OF z_Hbz z_Hby z_Hdb z_Hdd z_Hm z_Hg z_Hdi])
  qed
 next
  assume z_Hmz:"(~?z_hmv)" (is "~~?z_hna")
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vx. (~(<<except(votes, self, ((votes[self]) \\cup {<<b, zenon_Vx>>})), except(maxBal, self, b)>>~=<<votes, maxBal>>)))" "bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1)))))" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hmz])
   assume z_Hbc:"bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1)))))" (is "?z_hbc")
   assume z_Hnk:"(~(<<except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))>>})), except(maxBal, self, b)>>~=<<votes, maxBal>>))" (is "~~?z_hnn")
   have z_Hnn: "?z_hnn" (is "?z_hnm=?z_hmx")
   by (rule zenon_notnot_0 [OF z_Hnk])
   have z_Hno: "(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))>>}))=votes)" (is "?z_hhs=_")
   using z_Hnn by auto
   show FALSE
   proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vo. (except(votes, self, ((votes[self]) \\cup {<<b, zenon_Vo>>}))~=votes))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hbr])
    assume z_Hbc:"?z_hbc"
    assume z_Hnw:"(?z_hhs~=votes)"
    show FALSE
    by (rule notE [OF z_Hnw z_Hno])
   next
    assume z_Hdb:"(~?z_hbc)"
    assume z_Hnx:"(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))>>}))~=votes)" (is "?z_hhy~=_")
    show FALSE
    by (rule notE [OF z_Hdb z_Hbc])
   qed
  next
   assume z_Hdb:"(~bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))))" (is "~?z_hbc")
   assume z_Hny:"(~(<<except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))>>})), except(maxBal, self, b)>>~=<<votes, maxBal>>))" (is "~~?z_hob")
   have z_Hob: "?z_hob" (is "?z_hoa=?z_hmx")
   by (rule zenon_notnot_0 [OF z_Hny])
   have z_Hoc: "(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))>>}))=votes)" (is "?z_hhy=_")
   using z_Hob by auto
   show FALSE
   proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vo. (except(votes, self, ((votes[self]) \\cup {<<b, zenon_Vo>>}))~=votes))" "?z_hbc" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hbr])
    assume z_Hbc:"?z_hbc"
    assume z_Hnw:"(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))>>}))~=votes)" (is "?z_hhs~=_")
    show FALSE
    by (rule notE [OF z_Hdb z_Hbc])
   next
    assume z_Hdb:"(~?z_hbc)"
    assume z_Hnx:"(?z_hhy~=votes)"
    show FALSE
    by (rule notE [OF z_Hnx z_Hoc])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1190"; *} qed
lemma ob'1189:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'140: "((\<exists> v \<in> (Value) : (((leq ((fapply ((maxBal), (self))), (b)))) & ((DidNotVoteIn ((self), (b)))) & (\<forall> p \<in> (((Acceptor) \\ ({(self)}))) : (\<forall> w \<in> (Value) : ((((VotedFor ((p), (b), (w)))) \<Rightarrow> (((w) = (v))))))) & ((SafeAt ((b), (v)))) & (((([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v_1. ((SafeAt ((b), (v_1))))))))>>)})))])) = ([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (v)>>)})))]))) & (((([(maxBal) EXCEPT ![(self)] = (b)])) = ([(maxBal) EXCEPT ![(self)] = (b)]))))) & (((<<(([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))])), (([(maxBal) EXCEPT ![(self)] = (b)]))>>) \<noteq> (<<(votes), (maxBal)>>))))"
shows "(\<exists>votesp : (\<exists>maxBalp : ((\<exists> v \<in> (Value) : (((leq ((fapply ((maxBal), (self))), (b)))) & ((DidNotVoteIn ((self), (b)))) & (\<forall> p \<in> (((Acceptor) \\ ({(self)}))) : (\<forall> w \<in> (Value) : ((((VotedFor ((p), (b), (w)))) \<Rightarrow> (((w) = (v))))))) & ((SafeAt ((b), (v)))) & (((votesp) = ([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (v)>>)})))]))) & (((maxBalp) = ([(maxBal) EXCEPT ![(self)] = (b)]))))) & (((<<(votesp), (maxBalp)>>) \<noteq> (<<(votes), (maxBal)>>))))))"(is "PROP ?ob'1189")
proof -
ML_command {* writeln "*** TLAPS ENTER 1189"; *}
show "PROP ?ob'1189"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_271b7f.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_271b7f.znn.out
;; obligation #1189
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'140" (/\ (TLA.bEx Value ((v) (/\ (arith.le (TLA.fapply maxBal self)
b) (DidNotVoteIn self b) (TLA.bAll (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bAll Value ((w) (=> (VotedFor p b w) (= w v))))))
(SafeAt b v) (= (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v_1) (SafeAt b v_1))))))))
(TLA.except votes self (TLA.cup (TLA.fapply votes self) (TLA.set (TLA.tuple b
v))))) (= (TLA.except maxBal self b) (TLA.except maxBal self b)))))
(-. (= (TLA.tuple (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))))))) (TLA.except maxBal self b))
(TLA.tuple votes
maxBal))))
$goal (E. ((votesp) (E. ((maxBalp) (/\ (TLA.bEx Value ((v) (/\ (arith.le (TLA.fapply maxBal self)
b) (DidNotVoteIn self b) (TLA.bAll (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bAll Value ((w) (=> (VotedFor p b w) (= w v))))))
(SafeAt b v) (= votesp
(TLA.except votes self (TLA.cup (TLA.fapply votes self) (TLA.set (TLA.tuple b
v))))) (= maxBalp (TLA.except maxBal self b))))) (-. (= (TLA.tuple votesp
maxBalp) (TLA.tuple votes
maxBal))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(bEx(Value, (\<lambda>v. (((maxBal[self]) <= b)&(DidNotVoteIn(self, b)&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=v))))))&(SafeAt(b, v)&((except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1))))>>}))=except(votes, self, ((votes[self]) \\cup {<<b, v>>})))&(except(maxBal, self, b)=except(maxBal, self, b)))))))))&(<<except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1))))>>})), except(maxBal, self, b)>>~=<<votes, maxBal>>))" (is "?z_hf&?z_hch")
 using v'140 by blast
 assume z_He:"(~(\\E votesp:(\\E maxBalp:(bEx(Value, (\<lambda>v. (((maxBal[self]) <= b)&(DidNotVoteIn(self, b)&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=v))))))&(SafeAt(b, v)&((votesp=except(votes, self, ((votes[self]) \\cup {<<b, v>>})))&(maxBalp=except(maxBal, self, b)))))))))&(<<votesp, maxBalp>>~=<<votes, maxBal>>)))))" (is "~(\\E x : ?z_hda(x))")
 have z_Hf: "?z_hf"
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hch: "?z_hch" (is "?z_hci~=?z_hcj")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hdb_z_Hf: "(\\E x:((x \\in Value)&(((maxBal[self]) <= b)&(DidNotVoteIn(self, b)&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1))))>>}))=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&(except(maxBal, self, b)=except(maxBal, self, b))))))))) == ?z_hf" (is "?z_hdb == _")
 by (unfold bEx_def)
 have z_Hdb: "?z_hdb" (is "\\E x : ?z_hdw(x)")
 by (unfold z_Hdb_z_Hf, fact z_Hf)
 have z_Hdx: "?z_hdw((CHOOSE x:((x \\in Value)&(((maxBal[self]) <= b)&(DidNotVoteIn(self, b)&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1))))>>}))=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&(except(maxBal, self, b)=except(maxBal, self, b))))))))))" (is "?z_hdz&?z_hea")
 by (rule zenon_ex_choose_0 [of "?z_hdw", OF z_Hdb])
 have z_Hdz: "?z_hdz"
 by (rule zenon_and_0 [OF z_Hdx])
 have z_Hea: "?z_hea" (is "?z_hj&?z_heb")
 by (rule zenon_and_1 [OF z_Hdx])
 have z_Hj: "?z_hj"
 by (rule zenon_and_0 [OF z_Hea])
 have z_Heb: "?z_heb" (is "?z_hp&?z_hec")
 by (rule zenon_and_1 [OF z_Hea])
 have z_Hp: "?z_hp"
 by (rule zenon_and_0 [OF z_Heb])
 have z_Hec: "?z_hec" (is "?z_hed&?z_hee")
 by (rule zenon_and_1 [OF z_Heb])
 have z_Hed: "?z_hed"
 by (rule zenon_and_0 [OF z_Hec])
 have z_Hee: "?z_hee" (is "?z_hef&?z_heg")
 by (rule zenon_and_1 [OF z_Hec])
 have z_Hef: "?z_hef"
 by (rule zenon_and_0 [OF z_Hee])
 have z_Heg: "?z_heg" (is "?z_heh&?z_hcf")
 by (rule zenon_and_1 [OF z_Hee])
 have z_Heh: "?z_heh" (is "?z_hbi=?z_hei")
 by (rule zenon_and_0 [OF z_Heg])
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vr. (except(votes, self, ((votes[self]) \\cup {<<b, zenon_Vr>>}))=?z_hei))" "bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1)))", OF z_Heh])
  assume z_Hbp:"bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))" (is "?z_hbp")
  assume z_Heq:"(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))>>}))=?z_hei)" (is "?z_her=_")
  have z_Hev_z_Heq: "(except(votes, self, ((votes[self]) \\cup {<<b, (CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))>>}))=?z_hei) == (?z_her=?z_hei)" (is "?z_hev == ?z_heq")
  by (unfold bChoose_def)
  have z_Hev: "?z_hev" (is "?z_hew=_")
  by (unfold z_Hev_z_Heq, fact z_Heq)
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vn. (<<except(votes, self, ((votes[self]) \\cup {<<b, zenon_Vn>>})), except(maxBal, self, b)>>~=?z_hcj))" "?z_hbp" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1)))", OF z_Hch])
   assume z_Hbp:"?z_hbp"
   assume z_Hfl:"(<<?z_her, except(maxBal, self, b)>>~=?z_hcj)" (is "?z_hfm~=_")
   have z_Hfn_z_Hfl: "(<<?z_hew, except(maxBal, self, b)>>~=?z_hcj) == (?z_hfm~=?z_hcj)" (is "?z_hfn == ?z_hfl")
   by (unfold bChoose_def)
   have z_Hfn: "?z_hfn" (is "?z_hfo~=_")
   by (unfold z_Hfn_z_Hfl, fact z_Hfl)
   have z_Hfp: "~?z_hda(?z_hew)" (is "~(\\E x : ?z_hfq(x))")
   by (rule zenon_notex_0 [of "?z_hda" "?z_hew", OF z_He])
   have z_Hfr: "~?z_hfq(except(maxBal, self, b))" (is "~(?z_hfs&_)")
   by (rule zenon_notex_0 [of "?z_hfq" "except(maxBal, self, b)", OF z_Hfp])
   show FALSE
   proof (rule zenon_notand [OF z_Hfr])
    assume z_Hft:"(~?z_hfs)"
    have z_Hfu_z_Hft: "(~(\\E x:((x \\in Value)&(?z_hj&(?z_hp&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((?z_hew=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&?z_hcf)))))))) == (~?z_hfs)" (is "?z_hfu == ?z_hft")
    by (unfold bEx_def)
    have z_Hfu: "?z_hfu" (is "~(\\E x : ?z_hgd(x))")
    by (unfold z_Hfu_z_Hft, fact z_Hft)
    have z_Hge: "~?z_hgd((CHOOSE x:((x \\in Value)&(?z_hj&(?z_hp&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((?z_hbi=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&?z_hcf))))))))" (is "~(_&?z_hgf)")
    by (rule zenon_notex_0 [of "?z_hgd" "(CHOOSE x:((x \\in Value)&(?z_hj&(?z_hp&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((?z_hbi=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&?z_hcf)))))))", OF z_Hfu])
    show FALSE
    proof (rule zenon_notand [OF z_Hge])
     assume z_Hgg:"(~?z_hdz)"
     show FALSE
     by (rule notE [OF z_Hgg z_Hdz])
    next
     assume z_Hgh:"(~?z_hgf)" (is "~(_&?z_hgi)")
     show FALSE
     proof (rule zenon_notand [OF z_Hgh])
      assume z_Hgj:"(~?z_hj)"
      show FALSE
      by (rule notE [OF z_Hgj z_Hj])
     next
      assume z_Hgk:"(~?z_hgi)" (is "~(_&?z_hgl)")
      show FALSE
      proof (rule zenon_notand [OF z_Hgk])
       assume z_Hgm:"(~?z_hp)"
       show FALSE
       by (rule notE [OF z_Hgm z_Hp])
      next
       assume z_Hgn:"(~?z_hgl)" (is "~(_&?z_hgo)")
       show FALSE
       proof (rule zenon_notand [OF z_Hgn])
        assume z_Hgp:"(~?z_hed)"
        show FALSE
        by (rule notE [OF z_Hgp z_Hed])
       next
        assume z_Hgq:"(~?z_hgo)" (is "~(_&?z_hgr)")
        show FALSE
        proof (rule zenon_notand [OF z_Hgq])
         assume z_Hgs:"(~?z_hef)"
         show FALSE
         by (rule notE [OF z_Hgs z_Hef])
        next
         assume z_Hgt:"(~?z_hgr)"
         show FALSE
         proof (rule zenon_notand [OF z_Hgt])
          assume z_Hgu:"(?z_hew~=?z_hei)"
          show FALSE
          by (rule notE [OF z_Hgu z_Hev])
         next
          assume z_Hgv:"(except(maxBal, self, b)~=except(maxBal, self, b))" (is "?z_hcg~=_")
          show FALSE
          by (rule zenon_noteq [OF z_Hgv])
         qed
        qed
       qed
      qed
     qed
    qed
   next
    assume z_Hgw:"(~?z_hfn)" (is "~~?z_hgx")
    show FALSE
    by (rule notE [OF z_Hgw z_Hfn])
   qed
  next
   assume z_Hgy:"(~?z_hbp)"
   assume z_Hgz:"(<<except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1)))>>})), except(maxBal, self, b)>>~=?z_hcj)" (is "?z_hha~=_")
   show FALSE
   by (rule notE [OF z_Hgy z_Hbp])
  qed
 next
  assume z_Hgy:"(~bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))))" (is "~?z_hbp")
  assume z_Hhf:"(except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1)))>>}))=?z_hei)" (is "?z_hhb=_")
  have z_Hhg_z_Hhf: "(except(votes, self, ((votes[self]) \\cup {<<b, (CHOOSE x:((x \\in Value)&SafeAt(b, x)))>>}))=?z_hei) == (?z_hhb=?z_hei)" (is "?z_hhg == ?z_hhf")
  by (unfold bChoose_def)
  have z_Hhg: "?z_hhg" (is "?z_hhh=_")
  by (unfold z_Hhg_z_Hhf, fact z_Hhf)
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vn. (<<except(votes, self, ((votes[self]) \\cup {<<b, zenon_Vn>>})), except(maxBal, self, b)>>~=?z_hcj))" "?z_hbp" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v_1. SafeAt(b, v_1)))", OF z_Hch])
   assume z_Hbp:"?z_hbp"
   assume z_Hfl:"(<<except(votes, self, ((votes[self]) \\cup {<<b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))>>})), except(maxBal, self, b)>>~=?z_hcj)" (is "?z_hfm~=_")
   show FALSE
   by (rule notE [OF z_Hgy z_Hbp])
  next
   assume z_Hgy:"(~?z_hbp)"
   assume z_Hgz:"(<<?z_hhb, except(maxBal, self, b)>>~=?z_hcj)" (is "?z_hha~=_")
   have z_Hhn_z_Hgz: "(<<?z_hhh, except(maxBal, self, b)>>~=?z_hcj) == (?z_hha~=?z_hcj)" (is "?z_hhn == ?z_hgz")
   by (unfold bChoose_def)
   have z_Hhn: "?z_hhn" (is "?z_hho~=_")
   by (unfold z_Hhn_z_Hgz, fact z_Hgz)
   have z_Hhp: "~?z_hda(?z_hhh)" (is "~(\\E x : ?z_hhq(x))")
   by (rule zenon_notex_0 [of "?z_hda" "?z_hhh", OF z_He])
   have z_Hhr: "~?z_hhq(except(maxBal, self, b))" (is "~(?z_hhs&_)")
   by (rule zenon_notex_0 [of "?z_hhq" "except(maxBal, self, b)", OF z_Hhp])
   show FALSE
   proof (rule zenon_notand [OF z_Hhr])
    assume z_Hht:"(~?z_hhs)"
    have z_Hhu_z_Hht: "(~(\\E x:((x \\in Value)&(?z_hj&(?z_hp&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((?z_hhh=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&?z_hcf)))))))) == (~?z_hhs)" (is "?z_hhu == ?z_hht")
    by (unfold bEx_def)
    have z_Hhu: "?z_hhu" (is "~(\\E x : ?z_hid(x))")
    by (unfold z_Hhu_z_Hht, fact z_Hht)
    have z_Hie: "~?z_hid((CHOOSE x:((x \\in Value)&(?z_hj&(?z_hp&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((?z_hbi=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&?z_hcf))))))))" (is "~(_&?z_hif)")
    by (rule zenon_notex_0 [of "?z_hid" "(CHOOSE x:((x \\in Value)&(?z_hj&(?z_hp&(bAll((Acceptor \\ {self}), (\<lambda>p. bAll(Value, (\<lambda>w. (VotedFor(p, b, w)=>(w=x))))))&(SafeAt(b, x)&((?z_hbi=except(votes, self, ((votes[self]) \\cup {<<b, x>>})))&?z_hcf)))))))", OF z_Hhu])
    show FALSE
    proof (rule zenon_notand [OF z_Hie])
     assume z_Hgg:"(~?z_hdz)"
     show FALSE
     by (rule notE [OF z_Hgg z_Hdz])
    next
     assume z_Hig:"(~?z_hif)" (is "~(_&?z_hih)")
     show FALSE
     proof (rule zenon_notand [OF z_Hig])
      assume z_Hgj:"(~?z_hj)"
      show FALSE
      by (rule notE [OF z_Hgj z_Hj])
     next
      assume z_Hii:"(~?z_hih)" (is "~(_&?z_hij)")
      show FALSE
      proof (rule zenon_notand [OF z_Hii])
       assume z_Hgm:"(~?z_hp)"
       show FALSE
       by (rule notE [OF z_Hgm z_Hp])
      next
       assume z_Hik:"(~?z_hij)" (is "~(_&?z_hil)")
       show FALSE
       proof (rule zenon_notand [OF z_Hik])
        assume z_Hgp:"(~?z_hed)"
        show FALSE
        by (rule notE [OF z_Hgp z_Hed])
       next
        assume z_Him:"(~?z_hil)" (is "~(_&?z_hin)")
        show FALSE
        proof (rule zenon_notand [OF z_Him])
         assume z_Hgs:"(~?z_hef)"
         show FALSE
         by (rule notE [OF z_Hgs z_Hef])
        next
         assume z_Hio:"(~?z_hin)"
         show FALSE
         proof (rule zenon_notand [OF z_Hio])
          assume z_Hip:"(?z_hhh~=?z_hei)"
          show FALSE
          by (rule notE [OF z_Hip z_Hhg])
         next
          assume z_Hgv:"(except(maxBal, self, b)~=except(maxBal, self, b))" (is "?z_hcg~=_")
          show FALSE
          by (rule zenon_noteq [OF z_Hgv])
         qed
        qed
       qed
      qed
     qed
    qed
   next
    assume z_Hiq:"(~?z_hhn)" (is "~~?z_hir")
    show FALSE
    by (rule notE [OF z_Hiq z_Hhn])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1189"; *} qed
lemma ob'1162:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'138: "((~ ((greater ((b), (b))))))"
assumes v'139: "((((((VInv) \<and> (\<forall> a \<in> (Q) : (((fapply ((maxBal), (a))) = (b)))))) \<and> ((~ (\<exists> v \<in> (Value) : ((VotedFor ((self), (b), (v))))))))) & (\<exists> self_1 \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : (((BallotAction ((self_1), (a_ca)))) & (((((self_1) \<in> (Q))) \<Rightarrow> ((leq ((a_ca), (b))))))))) & ((BallotAction ((self), (b)))))"
assumes v'140: "((greater ((b), (fapply ((maxBal), (self))))))"
assumes v'141: "((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(self)] = (b)])))"
assumes v'142: "((((a_voteshash_primea :: c)) = (votes)))"
shows "((((((a_hd9c756012e3648df0482d0847d2832a :: c)) \<and> (\<forall> a \<in> (Q) : (((fapply (((a_maxBalhash_primea :: c)), (a))) = (b)))))) \<and> (\<exists> v \<in> (Value) : ((a_hedffe1caafe019043ade750241d505a ((self), (b), (v)) :: c)))))"(is "PROP ?ob'1162")
proof -
ML_command {* writeln "*** TLAPS ENTER 1162"; *}
show "PROP ?ob'1162"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_7c15e5.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_7c15e5.znn.out
;; obligation #1162
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'138" (-. (arith.lt b b))
$hyp "v'139" (/\ (/\ (/\ VInv (TLA.bAll Q ((a) (= (TLA.fapply maxBal a) b))))
(-. (TLA.bEx Value ((v) (VotedFor self b v)))))
(TLA.bEx Acceptor ((self_1) (TLA.bEx Ballot ((a_ca) (/\ (BallotAction self_1
a_ca) (=> (TLA.in self_1 Q) (arith.le a_ca b))))))) (BallotAction self
b))
$hyp "v'140" (arith.lt (TLA.fapply maxBal self)
b)
$hyp "v'141" (= a_maxBalhash_primea
(TLA.except maxBal self b))
$hyp "v'142" (= a_voteshash_primea
votes)
$goal (/\ (/\ a_hd9c756012e3648df0482d0847d2832a
(TLA.bAll Q ((a) (= (TLA.fapply a_maxBalhash_primea a) b))))
(TLA.bEx Value ((v) (a_hedffe1caafe019043ade750241d505a self b
v))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(((VInv&bAll(Q, (\<lambda>a. ((maxBal[a])=b))))&(~bEx(Value, (\<lambda>v. VotedFor(self, b, v)))))&(bEx(Acceptor, (\<lambda>self_1. bEx(Ballot, (\<lambda>a_ca. (BallotAction(self_1, a_ca)&((self_1 \\in Q)=>(a_ca <= b)))))))&BallotAction(self, b)))" (is "?z_hj&?z_hbb")
 using v'139 by blast
 have z_Hd:"(~(b < b))" (is "~?z_hbq")
 using v'138 by blast
 have z_Hf:"((maxBal[self]) < b)" (is "?z_hf")
 using v'140 by blast
 have z_Hc:"(self \\in Q)" (is "?z_hc")
 using self_in by blast
 assume z_Hi:"(~((a_hd9c756012e3648df0482d0847d2832a&bAll(Q, (\<lambda>a. ((a_maxBalhash_primea[a])=b))))&bEx(Value, (\<lambda>v. a_hedffe1caafe019043ade750241d505a(self, b, v)))))" (is "~(?z_hbt&?z_hca)")
 have z_Hj: "?z_hj" (is "?z_hk&?z_hu")
 by (rule zenon_and_0 [OF z_He])
 have z_Hk: "?z_hk" (is "_&?z_hm")
 by (rule zenon_and_0 [OF z_Hj])
 have z_Hm: "?z_hm"
 by (rule zenon_and_1 [OF z_Hk])
 show FALSE
 proof (rule notE [OF z_Hd])
  have z_Hcd: "((maxBal[self])=b)" (is "?z_hbr=_")
  proof (rule zenon_nnpp [of "(?z_hbr=b)"])
   assume z_Hce:"(?z_hbr~=b)"
   have z_Hcd: "(?z_hbr=b)"
   by (rule zenon_all_in_0 [of "Q" "(\<lambda>a. ((maxBal[a])=b))", OF z_Hm z_Hc])
   show FALSE
   by (rule notE [OF z_Hce z_Hcd])
  qed
  have z_Hbq: "?z_hbq"
  by (rule subst [where P="(\<lambda>zenon_Vg. (zenon_Vg < b))", OF z_Hcd], fact z_Hf)
  thus "?z_hbq" .
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1162"; *} qed
lemma ob'1207:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'149: "((((((((((((((votes) \<in> ([(Acceptor) \<rightarrow> ((SUBSET (((Ballot) \<times> (Value)))))]))) & (((maxBal) \<in> ([(Acceptor) \<rightarrow> (((Ballot) \<union> ({((minus (((Succ[0])))))})))])))) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))) \<and> (\<forall> a \<in> (Q) : (((fapply ((maxBal), (a))) = (b)))))) \<and> ((~ (\<exists> v \<in> (Value) : ((VotedFor ((self), (b), (v)))))))))"
assumes v'150: "((\<forall> Q_1 \<in> (Quorum) : (((Q_1) \<subseteq> (Acceptor)))) & (\<forall> a_Q1a \<in> (Quorum) : (\<forall> a_Q2a \<in> (Quorum) : (((((a_Q1a) \<inter> (a_Q2a))) \<noteq> ({}))))))"
shows "(((fapply (([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))]), (self))) = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))))"(is "PROP ?ob'1207")
proof -
ML_command {* writeln "*** TLAPS ENTER 1207"; *}
show "PROP ?ob'1207"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_ee4e02.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_ee4e02.znn.out
;; obligation #1207
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'149" (/\ (/\ (/\ (/\ (/\ (/\ (TLA.in votes
(TLA.FuncSet Acceptor (TLA.SUBSET (TLA.prod Ballot Value)))) (TLA.in maxBal
(TLA.FuncSet Acceptor (TLA.cup Ballot
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0))))))) a_VInv2a) a_VInv3a)
a_VInv4a) (TLA.bAll Q ((a) (= (TLA.fapply maxBal a) b))))
(-. (TLA.bEx Value ((v) (VotedFor self b
v)))))
$hyp "v'150" (/\ (TLA.bAll Quorum ((Q_1) (TLA.subseteq Q_1 Acceptor)))
(TLA.bAll Quorum ((a_Q1a) (TLA.bAll Quorum ((a_Q2a) (-. (= (TLA.cap a_Q1a
a_Q2a)
TLA.emptyset)))))))
$goal (= (TLA.fapply (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))))))) self)
(TLA.cup (TLA.fapply votes self) (TLA.set (TLA.tuple b
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b
v))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(((((((votes \\in FuncSet(Acceptor, SUBSET(prod(Ballot, Value))))&(maxBal \\in FuncSet(Acceptor, (Ballot \\cup { -.(1)}))))&a_VInv2a)&a_VInv3a)&a_VInv4a)&bAll(Q, (\<lambda>a. ((maxBal[a])=b))))&(~bEx(Value, (\<lambda>v. VotedFor(self, b, v)))))" (is "?z_hg&?z_hbk")
 using v'149 by blast
 have z_He:"(bAll(Quorum, (\<lambda>Q_1. (Q_1 \\subseteq Acceptor)))&bAll(Quorum, (\<lambda>a_Q1a. bAll(Quorum, (\<lambda>a_Q2a. ((a_Q1a \\cap a_Q2a)~={}))))))" (is "?z_hbq&?z_hbv")
 using v'150 by blast
 have z_Ha:"(Q \\in Quorum)" (is "?z_ha")
 using Q_in by blast
 have z_Hc:"(self \\in Q)" (is "?z_hc")
 using self_in by blast
 assume z_Hf:"((except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))[self])~=((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))" (is "?z_hce~=?z_hcg")
 have z_Hg: "?z_hg" (is "?z_hh&?z_hbd")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hh: "?z_hh" (is "?z_hi&_")
 by (rule zenon_and_0 [OF z_Hg])
 have z_Hi: "?z_hi" (is "?z_hj&_")
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hj: "?z_hj" (is "?z_hk&_")
 by (rule zenon_and_0 [OF z_Hi])
 have z_Hk: "?z_hk" (is "?z_hl&?z_ht")
 by (rule zenon_and_0 [OF z_Hj])
 have z_Hl: "?z_hl"
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hbq: "?z_hbq"
 by (rule zenon_and_0 [OF z_He])
 have z_Hdb_z_Hl: "(votes \\in FuncSet(Acceptor, SUBSET(Product(<<Ballot, Value>>)))) == ?z_hl" (is "?z_hdb == _")
 by (unfold prod_def)
 have z_Hdb: "?z_hdb"
 by (unfold z_Hdb_z_Hl, fact z_Hl)
 have z_Hdg: "(DOMAIN(votes)=Acceptor)" (is "?z_hdh=_")
 by (rule zenon_in_funcset_1 [of "votes" "Acceptor" "SUBSET(Product(<<Ballot, Value>>))", OF z_Hdb])
 show FALSE
 proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hcg))" "votes" "self" "?z_hcg" "self", OF z_Hf])
  assume z_Hdl:"(self \\in ?z_hdh)" (is "?z_hdl")
  assume z_Hdm:"(self=self)"
  assume z_Hdn:"(?z_hcg~=?z_hcg)"
  show FALSE
  by (rule zenon_noteq [OF z_Hdn])
 next
  assume z_Hdl:"(self \\in ?z_hdh)" (is "?z_hdl")
  assume z_Hdo:"(self~=self)"
  assume z_Hdp:"((votes[self])~=?z_hcg)" (is "?z_hch~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hdo])
 next
  assume z_Hdq:"(~(self \\in ?z_hdh))" (is "~?z_hdl")
  have z_Hdr: "(Q \\subseteq Acceptor)" (is "?z_hdr")
  by (rule zenon_all_in_0 [of "Quorum" "(\<lambda>Q_1. (Q_1 \\subseteq Acceptor))", OF z_Hbq z_Ha])
  have z_Hds_z_Hdr: "bAll(Q, (\<lambda>x. (x \\in Acceptor))) == ?z_hdr" (is "?z_hds == _")
  by (unfold subset_def)
  have z_Hds: "?z_hds"
  by (unfold z_Hds_z_Hdr, fact z_Hdr)
  have z_Hdw_z_Hds: "(\\A x:((x \\in Q)=>(x \\in Acceptor))) == ?z_hds" (is "?z_hdw == _")
  by (unfold bAll_def)
  have z_Hdw: "?z_hdw" (is "\\A x : ?z_hdz(x)")
  by (unfold z_Hdw_z_Hds, fact z_Hds)
  have z_Hea: "?z_hdz(self)" (is "_=>?z_heb")
  by (rule zenon_all_0 [of "?z_hdz" "self", OF z_Hdw])
  show FALSE
  proof (rule zenon_imply [OF z_Hea])
   assume z_Hec:"(~?z_hc)"
   show FALSE
   by (rule notE [OF z_Hec z_Hc])
  next
   assume z_Heb:"?z_heb"
   have z_Hdl: "?z_hdl"
   by (rule ssubst [where P="(\<lambda>zenon_Vk. (self \\in zenon_Vk))", OF z_Hdg z_Heb])
   show FALSE
   by (rule notE [OF z_Hdq z_Hdl])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1207"; *} qed
lemma ob'1203:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'152: "(((<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>) \<in> (fapply (([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))]), (self)))))"
assumes v'153: "(\<forall> w \<in> (Value) : (((<<(b), (w)>>) \<notin> (fapply ((votes), (self))))))"
assumes v'154: "(((((cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))) \<in> (Value))) \<and> ((SafeAt ((b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v)))))))))))))"
shows "((([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))]) \<noteq> (votes)))"(is "PROP ?ob'1203")
proof -
ML_command {* writeln "*** TLAPS ENTER 1203"; *}
show "PROP ?ob'1203"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_376df6.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_376df6.znn.out
;; obligation #1203
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'152" (TLA.in (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))))
(TLA.fapply (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b
v)))))))) self))
$hyp "v'153" (TLA.bAll Value ((w) (-. (TLA.in (TLA.tuple b w)
(TLA.fapply votes self)))))
$hyp "v'154" (/\ (TLA.in (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v)))) Value) (SafeAt b
(TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b
v))))))
$goal (-. (= (TLA.except votes self (TLA.cup (TLA.fapply votes self)
(TLA.set (TLA.tuple b (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w) (VotedFor p b
w))))) (TLA.bChoice Value ((w) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p) (TLA.bEx Value ((w_1) (VotedFor p b w_1))))) b
w))) (TLA.bChoice Value ((v) (SafeAt b v))))))))
votes))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"bAll(Value, (\<lambda>w. (~(<<b, w>> \\in (votes[self])))))" (is "?z_hf")
 using v'153 by blast
 have z_He:"(<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>> \\in (except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))[self]))" (is "?z_he")
 using v'152 by blast
 have z_Hg:"((cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))) \\in Value)&SafeAt(b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))))" (is "?z_hbp&?z_hbq")
 using v'154 by blast
 have zenon_L1_: "((except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))[self])~=(votes[self])) ==> (~(except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))~=votes)) ==> FALSE" (is "?z_hbr ==> ?z_hh ==> FALSE")
 proof -
  assume z_Hbr:"?z_hbr" (is "?z_hbl~=?z_hp")
  assume z_Hh:"?z_hh" (is "~~?z_hbt")
  show FALSE
  proof (rule zenon_noteq [of "?z_hp"])
   have z_Hbt: "?z_hbt" (is "?z_hbm=_")
   proof (rule zenon_nnpp [of "?z_hbt"])
    assume z_Hbs:"(?z_hbm~=votes)"
    show FALSE
    by (rule notE [OF z_Hh z_Hbs])
   qed
   have z_Hbu: "(?z_hp~=?z_hp)"
   by (rule subst [where P="(\<lambda>zenon_Vzd. ((zenon_Vzd[self])~=?z_hp))", OF z_Hbt], fact z_Hbr)
   thus "(?z_hp~=?z_hp)" .
  qed
 qed
 have zenon_L2_: "?z_hbp ==> (\\A x:((x \\in Value)=>(~(<<b, x>> \\in (votes[self]))))) ==> ?z_he ==> (~(except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))~=votes)) ==> bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))) ==> FALSE" (is "_ ==> ?z_ha ==> _ ==> ?z_hh ==> ?z_hu ==> FALSE")
 proof -
  assume z_Hbp:"?z_hbp"
  assume z_Ha:"?z_ha" (is "\\A x : ?z_hcf(x)")
  assume z_He:"?z_he"
  assume z_Hh:"?z_hh" (is "~~?z_hbt")
  assume z_Hu:"?z_hu"
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vs. (zenon_Vs \\in Value))" "?z_hu" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hbp])
   assume z_Hu:"?z_hu"
   assume z_Hcj:"(bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))) \\in Value)" (is "?z_hcj")
   have z_Hck_z_Hcj: "((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))) \\in Value) == ?z_hcj" (is "?z_hck == _")
   by (unfold bChoose_def)
   have z_Hck: "?z_hck"
   by (unfold z_Hck_z_Hcj, fact z_Hcj)
   have z_Hco: "?z_hcf((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x))))" (is "_=>?z_hcp")
   by (rule zenon_all_0 [of "?z_hcf" "(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))", OF z_Ha])
   show FALSE
   proof (rule zenon_imply [OF z_Hco])
    assume z_Hcq:"(~?z_hck)"
    show FALSE
    by (rule notE [OF z_Hcq z_Hck])
   next
    assume z_Hcp:"?z_hcp" (is "~?z_hcr")
    show FALSE
    proof (rule notE [OF z_Hcp])
     have z_Hcs: "(<<b, cond(?z_hu, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>=<<b, (CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, x)))>>)" (is "?z_hs=?z_hct")
     proof (rule zenon_nnpp [of "(?z_hs=?z_hct)"])
      assume z_Hcu:"(?z_hs~=?z_hct)"
      show FALSE
      proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vod. (<<b, zenon_Vod>>~=?z_hct))" "?z_hu" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hcu])
       assume z_Hu:"?z_hu"
       assume z_Hcz:"(<<b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))>>~=?z_hct)" (is "?z_hda~=_")
       have z_Hdb_z_Hcz: "(?z_hct~=?z_hct) == (?z_hda~=?z_hct)" (is "?z_hdb == ?z_hcz")
       by (unfold bChoose_def)
       have z_Hdb: "?z_hdb"
       by (unfold z_Hdb_z_Hcz, fact z_Hcz)
       show FALSE
       by (rule zenon_noteq [OF z_Hdb])
      next
       assume z_Hdc:"(~?z_hu)"
       assume z_Hdd:"(<<b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))>>~=?z_hct)" (is "?z_hde~=_")
       show FALSE
       by (rule notE [OF z_Hdc z_Hu])
      qed
     qed
     have z_Hdf: "((except(votes, self, ((votes[self]) \\cup {?z_hs}))[self])=(votes[self]))" (is "?z_hbl=?z_hp")
     proof (rule zenon_nnpp [of "(?z_hbl=?z_hp)"])
      assume z_Hbr:"(?z_hbl~=?z_hp)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hbr z_Hh])
     qed
     have z_Hdg: "(?z_hct \\in ?z_hbl)" (is "?z_hdg")
     by (rule subst [where P="(\<lambda>zenon_Vi. (zenon_Vi \\in ?z_hbl))", OF z_Hcs], fact z_He)
     have z_Hcr: "?z_hcr"
     by (rule subst [where P="(\<lambda>zenon_Vbd. (?z_hct \\in zenon_Vbd))", OF z_Hdf], fact z_Hdg)
     thus "?z_hcr" .
    qed
   qed
  next
   assume z_Hdc:"(~?z_hu)"
   assume z_Hdn:"(bChoice(Value, (\<lambda>v. SafeAt(b, v))) \\in Value)" (is "?z_hdn")
   show FALSE
   by (rule notE [OF z_Hdc z_Hu])
  qed
 qed
 have zenon_L3_: "?z_hbp ==> (\\A x:((x \\in Value)=>(~(<<b, x>> \\in (votes[self]))))) ==> ?z_he ==> (~(except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))~=votes)) ==> (~bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))) ==> FALSE" (is "_ ==> ?z_ha ==> _ ==> ?z_hh ==> ?z_hdc ==> FALSE")
 proof -
  assume z_Hbp:"?z_hbp"
  assume z_Ha:"?z_ha" (is "\\A x : ?z_hcf(x)")
  assume z_He:"?z_he"
  assume z_Hh:"?z_hh" (is "~~?z_hbt")
  assume z_Hdc:"?z_hdc" (is "~?z_hu")
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vs. (zenon_Vs \\in Value))" "?z_hu" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hbp])
   assume z_Hu:"?z_hu"
   assume z_Hcj:"(bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))) \\in Value)" (is "?z_hcj")
   show FALSE
   by (rule notE [OF z_Hdc z_Hu])
  next
   assume z_Hdc:"?z_hdc"
   assume z_Hdn:"(bChoice(Value, (\<lambda>v. SafeAt(b, v))) \\in Value)" (is "?z_hdn")
   have z_Hdo_z_Hdn: "((CHOOSE x:((x \\in Value)&SafeAt(b, x))) \\in Value) == ?z_hdn" (is "?z_hdo == _")
   by (unfold bChoose_def)
   have z_Hdo: "?z_hdo"
   by (unfold z_Hdo_z_Hdn, fact z_Hdn)
   have z_Hds: "?z_hcf((CHOOSE x:((x \\in Value)&SafeAt(b, x))))" (is "_=>?z_hdt")
   by (rule zenon_all_0 [of "?z_hcf" "(CHOOSE x:((x \\in Value)&SafeAt(b, x)))", OF z_Ha])
   show FALSE
   proof (rule zenon_imply [OF z_Hds])
    assume z_Hdu:"(~?z_hdo)"
    show FALSE
    by (rule notE [OF z_Hdu z_Hdo])
   next
    assume z_Hdt:"?z_hdt" (is "~?z_hdv")
    show FALSE
    proof (rule notE [OF z_Hdt])
     have z_Hdw: "(<<b, cond(?z_hu, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>=<<b, (CHOOSE x:((x \\in Value)&SafeAt(b, x)))>>)" (is "?z_hs=?z_hdx")
     proof (rule zenon_nnpp [of "(?z_hs=?z_hdx)"])
      assume z_Hdy:"(?z_hs~=?z_hdx)"
      show FALSE
      proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vkb. (<<b, zenon_Vkb>>~=?z_hdx))" "?z_hu" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hdy])
       assume z_Hu:"?z_hu"
       assume z_Hed:"(<<b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))>>~=?z_hdx)" (is "?z_hda~=_")
       show FALSE
       by (rule notE [OF z_Hdc z_Hu])
      next
       assume z_Hdc:"?z_hdc"
       assume z_Hee:"(<<b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))>>~=?z_hdx)" (is "?z_hde~=_")
       have z_Hef_z_Hee: "(?z_hdx~=?z_hdx) == (?z_hde~=?z_hdx)" (is "?z_hef == ?z_hee")
       by (unfold bChoose_def)
       have z_Hef: "?z_hef"
       by (unfold z_Hef_z_Hee, fact z_Hee)
       show FALSE
       by (rule zenon_noteq [OF z_Hef])
      qed
     qed
     have z_Hdf: "((except(votes, self, ((votes[self]) \\cup {?z_hs}))[self])=(votes[self]))" (is "?z_hbl=?z_hp")
     proof (rule zenon_nnpp [of "(?z_hbl=?z_hp)"])
      assume z_Hbr:"(?z_hbl~=?z_hp)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hbr z_Hh])
     qed
     have z_Heg: "(?z_hdx \\in ?z_hbl)" (is "?z_heg")
     by (rule subst [where P="(\<lambda>zenon_Vi. (zenon_Vi \\in ?z_hbl))", OF z_Hdw], fact z_He)
     have z_Hdv: "?z_hdv"
     by (rule subst [where P="(\<lambda>zenon_Vde. (?z_hdx \\in zenon_Vde))", OF z_Hdf], fact z_Heg)
     thus "?z_hdv" .
    qed
   qed
  qed
 qed
 assume z_Hh:"(~(except(votes, self, ((votes[self]) \\cup {<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>}))~=votes))" (is "~~?z_hbt")
 have z_Ha_z_Hf: "(\\A x:((x \\in Value)=>(~(<<b, x>> \\in (votes[self]))))) == ?z_hf" (is "?z_ha == _")
 by (unfold bAll_def)
 have z_Ha: "?z_ha" (is "\\A x : ?z_hcf(x)")
 by (unfold z_Ha_z_Hf, fact z_Hf)
 have z_Hbp: "?z_hbp"
 by (rule zenon_and_0 [OF z_Hg])
 have z_Hek: "?z_hcf((CHOOSE x : TRUE))" (is "?z_hem=>?z_hen")
 by (rule zenon_all_0 [of "?z_hcf" "(CHOOSE x : TRUE)", OF z_Ha])
 show FALSE
 proof (rule zenon_imply [OF z_Hek])
  assume z_Heo:"(~?z_hem)"
  show FALSE
  proof (rule notE [OF z_Heo])
   have z_Hep: "(cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))=(CHOOSE x : TRUE))" (is "?z_ht=?z_hel")
   proof (rule zenon_nnpp [of "(?z_ht=?z_hel)"])
    assume z_Heq:"(?z_ht~=?z_hel)"
    show FALSE
    proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Via. (zenon_Via~=?z_hel))" "bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Heq])
     assume z_Hu:"bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))" (is "?z_hu")
     assume z_Heu:"(bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))~=?z_hel)" (is "?z_hbd~=_")
     show FALSE
     by (rule zenon_L2_ [OF z_Hbp z_Ha z_He z_Hh z_Hu])
    next
     assume z_Hdc:"(~bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))))" (is "~?z_hu")
     assume z_Hev:"(bChoice(Value, (\<lambda>v. SafeAt(b, v)))~=?z_hel)" (is "?z_hbh~=_")
     show FALSE
     by (rule zenon_L3_ [OF z_Hbp z_Ha z_He z_Hh z_Hdc])
    qed
   qed
   have z_Hem: "?z_hem"
   by (rule subst [where P="(\<lambda>zenon_Vs. (zenon_Vs \\in Value))", OF z_Hep], fact z_Hbp)
   thus "?z_hem" .
  qed
 next
  assume z_Hen:"?z_hen" (is "~?z_hew")
  show FALSE
  proof (rule notE [OF z_Hen])
   have z_Hex: "(<<b, cond(bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w))), bChoice(Value, (\<lambda>v. SafeAt(b, v))))>>=<<b, (CHOOSE x : TRUE)>>)" (is "?z_hs=?z_hey")
   proof (rule zenon_nnpp [of "(?z_hs=?z_hey)"])
    assume z_Hez:"(?z_hs~=?z_hey)"
    show FALSE
    proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vy. (<<b, zenon_Vy>>~=?z_hey))" "bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))" "bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hez])
     assume z_Hu:"bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w)))))" (is "?z_hu")
     assume z_Hfe:"(<<b, bChoice(Value, (\<lambda>w. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))), b, w)))>>~=?z_hey)" (is "?z_hda~=_")
     show FALSE
     by (rule zenon_L2_ [OF z_Hbp z_Ha z_He z_Hh z_Hu])
    next
     assume z_Hdc:"(~bEx((Acceptor \\ {self}), (\<lambda>p. bEx(Value, (\<lambda>w. VotedFor(p, b, w))))))" (is "~?z_hu")
     assume z_Hff:"(<<b, bChoice(Value, (\<lambda>v. SafeAt(b, v)))>>~=?z_hey)" (is "?z_hde~=_")
     show FALSE
     by (rule zenon_L3_ [OF z_Hbp z_Ha z_He z_Hh z_Hdc])
    qed
   qed
   have z_Hdf: "((except(votes, self, ((votes[self]) \\cup {?z_hs}))[self])=(votes[self]))" (is "?z_hbl=?z_hp")
   proof (rule zenon_nnpp [of "(?z_hbl=?z_hp)"])
    assume z_Hbr:"(?z_hbl~=?z_hp)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hbr z_Hh])
   qed
   have z_Hfg: "(?z_hey \\in ?z_hbl)" (is "?z_hfg")
   by (rule subst [where P="(\<lambda>zenon_Vi. (zenon_Vi \\in ?z_hbl))", OF z_Hex], fact z_He)
   have z_Hew: "?z_hew"
   by (rule subst [where P="(\<lambda>zenon_Vge. (?z_hey \\in zenon_Vge))", OF z_Hdf], fact z_Hfg)
   thus "?z_hew" .
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1203"; *} qed
lemma ob'1199:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
fixes p
assumes p_in : "(p \<in> (((Acceptor) \\ ({(self)}))))"
fixes w
assumes w_in : "(w \<in> (Value))"
assumes v'149: "((VotedFor ((p), (b), (w))))"
assumes v'150: "(((\<exists> p_1 \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w_1 \<in> (Value) : ((VotedFor ((p_1), (b), (w_1)))))) \<Rightarrow> ((((bChoice((((Acceptor) \\ ({(self)}))), %p_1. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p_1), (b), (w_1))))))) \<in> (Acceptor))) & (((bChoice((Value), %w_1. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p_1. (\<exists> w_2 \<in> (Value) : ((VotedFor ((p_1), (b), (w_2))))))), (b), (w_1)))))) \<in> (Value))) & ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p_1. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p_1), (b), (w_1))))))), (b), (bChoice((Value), %w_1. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p_1. (\<exists> w_2 \<in> (Value) : ((VotedFor ((p_1), (b), (w_2))))))), (b), (w_1))))))))))))"
assumes v'151: "(((((((((((TypeOK) \<and> (a_VInv2a))) \<and> (\<forall> a_a1a \<in> (Acceptor) : (\<forall> a_a2a \<in> (Acceptor) : (\<forall> b_1 \<in> (Ballot) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : ((((((VotedFor ((a_a1a), (b_1), (a_v1a)))) \<and> ((VotedFor ((a_a2a), (b_1), (a_v2a)))))) \<Rightarrow> (((a_v1a) = (a_v2a)))))))))))) \<and> (a_VInv4a))) \<and> (\<forall> a \<in> (Q) : (((fapply ((maxBal), (a))) = (b)))))) \<and> ((~ (\<exists> v \<in> (Value) : ((VotedFor ((self), (b), (v)))))))))"
shows "(((w) = (cond((\<exists> p_1 \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w_1 \<in> (Value) : ((VotedFor ((p_1), (b), (w_1)))))), (bChoice((Value), %w_1. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p_1. (\<exists> w_2 \<in> (Value) : ((VotedFor ((p_1), (b), (w_2))))))), (b), (w_1)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))))"(is "PROP ?ob'1199")
proof -
ML_command {* writeln "*** TLAPS ENTER 1199"; *}
show "PROP ?ob'1199"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_a90b81.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_a90b81.znn.out
;; obligation #1199
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "p_in" (TLA.in p (TLA.setminus Acceptor
(TLA.set self)))
$hyp "w_in" (TLA.in w Value)
$hyp "v'149" (VotedFor p b w)
$hyp "v'150" (=> (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_1) (VotedFor p_1 b w_1)))))
(/\ (TLA.in (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_1) (VotedFor p_1 b w_1)))))
Acceptor)
(TLA.in (TLA.bChoice Value ((w_1) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_2) (VotedFor p_1 b w_2))))) b
w_1))) Value) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_1) (VotedFor p_1 b w_1))))) b
(TLA.bChoice Value ((w_1) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_2) (VotedFor p_1 b w_2))))) b
w_1))))))
$hyp "v'151" (/\ (/\ (/\ (/\ (/\ TypeOK a_VInv2a)
(TLA.bAll Acceptor ((a_a1a) (TLA.bAll Acceptor ((a_a2a) (TLA.bAll Ballot ((b_1) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (VotedFor a_a1a
b_1 a_v1a) (VotedFor a_a2a b_1 a_v2a)) (= a_v1a a_v2a))))))))))))) a_VInv4a)
(TLA.bAll Q ((a) (= (TLA.fapply maxBal a) b))))
(-. (TLA.bEx Value ((v) (VotedFor self b v)))))
$goal (= w (TLA.cond (TLA.bEx (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_1) (VotedFor p_1 b
w_1))))) (TLA.bChoice Value ((w_1) (VotedFor (TLA.bChoice (TLA.setminus Acceptor
(TLA.set self)) ((p_1) (TLA.bEx Value ((w_2) (VotedFor p_1 b w_2))))) b
w_1))) (TLA.bChoice Value ((v) (SafeAt b
v)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(w \\in Value)" (is "?z_he")
 using w_in by blast
 have z_Hf:"VotedFor(p, b, w)" (is "?z_hf")
 using v'149 by blast
 have z_Hd:"(p \\in (Acceptor \\ {self}))" (is "?z_hd")
 using p_in by blast
 have z_Hb:"(b \\in Ballot)" (is "?z_hb")
 using b_in by blast
 have z_Hg:"(bEx((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1)))))=>((bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))) \\in Acceptor)&((bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))) \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))))))" (is "?z_hs=>?z_hz")
 using v'150 by blast
 have z_Hh:"(((((TypeOK&a_VInv2a)&bAll(Acceptor, (\<lambda>a_a1a. bAll(Acceptor, (\<lambda>a_a2a. bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. ((VotedFor(a_a1a, b_1, a_v1a)&VotedFor(a_a2a, b_1, a_v2a))=>(a_v1a=a_v2a)))))))))))))&a_VInv4a)&bAll(Q, (\<lambda>a. ((maxBal[a])=b))))&(~bEx(Value, (\<lambda>v. VotedFor(self, b, v)))))" (is "?z_hbi&?z_hcq")
 using v'151 by blast
 have zenon_L1_: "(~(\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1)))))) ==> ?z_hd ==> ?z_hf ==> ?z_he ==> FALSE" (is "?z_hcv ==> _ ==> _ ==> _ ==> FALSE")
 proof -
  assume z_Hcv:"?z_hcv" (is "~(\\E x : ?z_hdd(x))")
  assume z_Hd:"?z_hd"
  assume z_Hf:"?z_hf"
  assume z_He:"?z_he"
  have z_Hde: "~?z_hdd(p)" (is "~(_&?z_hdf)")
  by (rule zenon_notex_0 [of "?z_hdd" "p", OF z_Hcv])
  show FALSE
  proof (rule zenon_notand [OF z_Hde])
   assume z_Hdg:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hdg z_Hd])
  next
   assume z_Hdh:"(~?z_hdf)"
   have z_Hdi_z_Hdh: "(~(\\E x:((x \\in Value)&VotedFor(p, b, x)))) == (~?z_hdf)" (is "?z_hdi == ?z_hdh")
   by (unfold bEx_def)
   have z_Hdi: "?z_hdi" (is "~(\\E x : ?z_hdn(x))")
   by (unfold z_Hdi_z_Hdh, fact z_Hdh)
   have z_Hdo: "~?z_hdn(w)"
   by (rule zenon_notex_0 [of "?z_hdn" "w", OF z_Hdi])
   show FALSE
   proof (rule zenon_notand [OF z_Hdo])
    assume z_Hdp:"(~?z_he)"
    show FALSE
    by (rule notE [OF z_Hdp z_He])
   next
    assume z_Hdq:"(~?z_hf)"
    show FALSE
    by (rule notE [OF z_Hdq z_Hf])
   qed
  qed
 qed
 have zenon_L2_: "(~?z_hs) ==> (\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))) ==> FALSE" (is "?z_hdr ==> ?z_hcw ==> FALSE")
 proof -
  assume z_Hdr:"?z_hdr"
  assume z_Hcw:"?z_hcw" (is "\\E x : ?z_hdd(x)")
  have z_Hcv_z_Hdr: "(~?z_hcw) == ?z_hdr" (is "?z_hcv == _")
  by (unfold bEx_def)
  have z_Hcv: "?z_hcv"
  by (unfold z_Hcv_z_Hdr, fact z_Hdr)
  show FALSE
  by (rule notE [OF z_Hcv z_Hcw])
 qed
 assume z_Hi:"(w~=cond(?z_hs, bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))), bChoice(Value, (\<lambda>v. SafeAt(b, v)))))" (is "_~=?z_hds")
 have z_Hdw: "(p \\in Acceptor)" (is "?z_hdw")
 by (rule zenon_in_setminus_0 [of "p" "Acceptor" "{self}", OF z_Hd])
 have z_Hbi: "?z_hbi" (is "?z_hbj&?z_hcj")
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hbj: "?z_hbj" (is "?z_hbk&_")
 by (rule zenon_and_0 [OF z_Hbi])
 have z_Hbk: "?z_hbk" (is "?z_hbl&?z_hbo")
 by (rule zenon_and_0 [OF z_Hbj])
 have z_Hbo: "?z_hbo"
 by (rule zenon_and_1 [OF z_Hbk])
 have z_Hdx_z_Hbo: "(\\A x:((x \\in Acceptor)=>bAll(Acceptor, (\<lambda>a_a2a. bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. ((VotedFor(x, b_1, a_v1a)&VotedFor(a_a2a, b_1, a_v2a))=>(a_v1a=a_v2a)))))))))))) == ?z_hbo" (is "?z_hdx == _")
 by (unfold bAll_def)
 have z_Hdx: "?z_hdx" (is "\\A x : ?z_hel(x)")
 by (unfold z_Hdx_z_Hbo, fact z_Hbo)
 show FALSE
 proof (rule zenon_imply [OF z_Hg])
  assume z_Hdr:"(~?z_hs)"
  have z_Hcv_z_Hdr: "(~(\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1)))))) == (~?z_hs)" (is "?z_hcv == ?z_hdr")
  by (unfold bEx_def)
  have z_Hcv: "?z_hcv" (is "~(\\E x : ?z_hdd(x))")
  by (unfold z_Hcv_z_Hdr, fact z_Hdr)
  show FALSE
  by (rule zenon_L1_ [OF z_Hcv z_Hd z_Hf z_He])
 next
  assume z_Hz:"?z_hz" (is "?z_hba&?z_hbc")
  have z_Hba: "?z_hba"
  by (rule zenon_and_0 [OF z_Hz])
  have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbh")
  by (rule zenon_and_1 [OF z_Hz])
  have z_Hbd: "?z_hbd"
  by (rule zenon_and_0 [OF z_Hbc])
  have z_Hem_z_Hba: "((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))) \\in Acceptor) == ?z_hba" (is "?z_hem == _")
  by (unfold bChoose_def)
  have z_Hem: "?z_hem"
  by (unfold z_Hem_z_Hba, fact z_Hba)
  have z_Heo_z_Hbd: "((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))) \\in Value) == ?z_hbd" (is "?z_heo == _")
  by (unfold bChoose_def)
  have z_Heo: "?z_heo"
  by (unfold z_Heo_z_Hbd, fact z_Hbd)
  show FALSE
  proof (rule zenon_em [of "(\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1)))))"])
   assume z_Hcw:"(\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1)))))" (is "\\E x : ?z_hdd(x)")
   have z_Hes: "?z_hdd((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))))" (is "?z_het&?z_heu")
   by (rule zenon_ex_choose_0 [of "?z_hdd", OF z_Hcw])
   have z_Heu: "?z_heu"
   by (rule zenon_and_1 [OF z_Hes])
   have z_Hev_z_Heu: "(\\E x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x))) == ?z_heu" (is "?z_hev == _")
   by (unfold bEx_def)
   have z_Hev: "?z_hev" (is "\\E x : ?z_hey(x)")
   by (unfold z_Hev_z_Heu, fact z_Heu)
   have z_Hez: "?z_hey((CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x))))" (is "?z_hfb&?z_hfc")
   by (rule zenon_ex_choose_0 [of "?z_hey", OF z_Hev])
   have z_Hfb: "?z_hfb"
   by (rule zenon_and_0 [OF z_Hez])
   have z_Hfc: "?z_hfc"
   by (rule zenon_and_1 [OF z_Hez])
   show FALSE
   proof (rule zenon_em [of "(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))"])
    assume z_Hfd:"(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))" (is "\\E x : ?z_hfe(x)")
    have z_Hff: "?z_hfe((CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))" (is "_&?z_hfg")
    by (rule zenon_ex_choose_0 [of "?z_hfe", OF z_Hfd])
    have z_Heo: "?z_heo"
    by (rule zenon_and_0 [OF z_Hff])
    have z_Hfg: "?z_hfg"
    by (rule zenon_and_1 [OF z_Hff])
    have z_Hfh_z_Hfg: "VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, (CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))) == ?z_hfg" (is "?z_hfh == _")
    by (unfold bChoose_def)
    have z_Hfh: "?z_hfh"
    by (unfold z_Hfh_z_Hfg, fact z_Hfg)
    show FALSE
    proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. (w~=zenon_Vf))" "?z_hs" "bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1)))" "bChoice(Value, (\<lambda>v. SafeAt(b, v)))", OF z_Hi])
     assume z_Hs:"?z_hs"
     assume z_Hfl:"(w~=bChoice(Value, (\<lambda>w_1. VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, w_1))))" (is "_~=?z_hbe")
     have z_Hfm_z_Hfl: "(w~=(CHOOSE x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x)))) == (w~=?z_hbe)" (is "?z_hfm == ?z_hfl")
     by (unfold bChoose_def)
     have z_Hfm: "?z_hfm" (is "_~=?z_hep")
     by (unfold z_Hfm_z_Hfl, fact z_Hfl)
     have z_Hfn: "?z_hel((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))))" (is "_=>?z_hfo")
     by (rule zenon_all_0 [of "?z_hel" "(CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1)))))", OF z_Hdx])
     show FALSE
     proof (rule zenon_imply [OF z_Hfn])
      assume z_Hfp:"(~?z_hem)"
      show FALSE
      by (rule notE [OF z_Hfp z_Hem])
     next
      assume z_Hfo:"?z_hfo"
      have z_Hfq_z_Hfo: "(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>b_1. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. ((VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b_1, a_v1a)&VotedFor(x, b_1, a_v2a))=>(a_v1a=a_v2a)))))))))) == ?z_hfo" (is "?z_hfq == _")
      by (unfold bAll_def)
      have z_Hfq: "?z_hfq" (is "\\A x : ?z_hgc(x)")
      by (unfold z_Hfq_z_Hfo, fact z_Hfo)
      have z_Hgd: "?z_hgc(p)" (is "_=>?z_hge")
      by (rule zenon_all_0 [of "?z_hgc" "p", OF z_Hfq])
      show FALSE
      proof (rule zenon_imply [OF z_Hgd])
       assume z_Hgf:"(~?z_hdw)"
       show FALSE
       by (rule notE [OF z_Hgf z_Hdw])
      next
       assume z_Hge:"?z_hge"
       have z_Hgg_z_Hge: "(\\A x:((x \\in Ballot)=>bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. ((VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), x, a_v1a)&VotedFor(p, x, a_v2a))=>(a_v1a=a_v2a)))))))) == ?z_hge" (is "?z_hgg == _")
       by (unfold bAll_def)
       have z_Hgg: "?z_hgg" (is "\\A x : ?z_hgr(x)")
       by (unfold z_Hgg_z_Hge, fact z_Hge)
       have z_Hgs: "?z_hgr(b)" (is "_=>?z_hgt")
       by (rule zenon_all_0 [of "?z_hgr" "b", OF z_Hgg])
       show FALSE
       proof (rule zenon_imply [OF z_Hgs])
        assume z_Hgu:"(~?z_hb)"
        show FALSE
        by (rule notE [OF z_Hgu z_Hb])
       next
        assume z_Hgt:"?z_hgt"
        have z_Hgv_z_Hgt: "(\\A x:((x \\in Value)=>bAll(Value, (\<lambda>a_v2a. ((VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x)&VotedFor(p, b, a_v2a))=>(x=a_v2a)))))) == ?z_hgt" (is "?z_hgv == _")
        by (unfold bAll_def)
        have z_Hgv: "?z_hgv" (is "\\A x : ?z_hhd(x)")
        by (unfold z_Hgv_z_Hgt, fact z_Hgt)
        have z_Hhe: "?z_hhd(?z_hep)" (is "_=>?z_hhf")
        by (rule zenon_all_0 [of "?z_hhd" "?z_hep", OF z_Hgv])
        show FALSE
        proof (rule zenon_imply [OF z_Hhe])
         assume z_Hhg:"(~?z_heo)"
         show FALSE
         by (rule notE [OF z_Hhg z_Heo])
        next
         assume z_Hhf:"?z_hhf"
         have z_Hhh_z_Hhf: "(\\A x:((x \\in Value)=>((?z_hfh&VotedFor(p, b, x))=>(?z_hep=x)))) == ?z_hhf" (is "?z_hhh == _")
         by (unfold bAll_def)
         have z_Hhh: "?z_hhh" (is "\\A x : ?z_hhm(x)")
         by (unfold z_Hhh_z_Hhf, fact z_Hhf)
         have z_Hhn: "?z_hhm(w)" (is "_=>?z_hho")
         by (rule zenon_all_0 [of "?z_hhm" "w", OF z_Hhh])
         show FALSE
         proof (rule zenon_imply [OF z_Hhn])
          assume z_Hdp:"(~?z_he)"
          show FALSE
          by (rule notE [OF z_Hdp z_He])
         next
          assume z_Hho:"?z_hho" (is "?z_hhp=>?z_hhq")
          show FALSE
          proof (rule zenon_imply [OF z_Hho])
           assume z_Hhr:"(~?z_hhp)"
           show FALSE
           proof (rule zenon_notand [OF z_Hhr])
            assume z_Hhs:"(~?z_hfh)"
            show FALSE
            by (rule notE [OF z_Hhs z_Hfh])
           next
            assume z_Hdq:"(~?z_hf)"
            show FALSE
            by (rule notE [OF z_Hdq z_Hf])
           qed
          next
           assume z_Hhq:"?z_hhq"
           show FALSE
           by (rule zenon_eqsym [OF z_Hhq z_Hfm])
          qed
         qed
        qed
       qed
      qed
     qed
    next
     assume z_Hdr:"(~?z_hs)"
     assume z_Hht:"(w~=bChoice(Value, (\<lambda>v. SafeAt(b, v))))" (is "_~=?z_hdt")
     show FALSE
     by (rule zenon_L2_ [OF z_Hdr z_Hcw])
    qed
   next
    assume z_Hhu:"(~(\\E x:((x \\in Value)&VotedFor(bChoice((Acceptor \\ {self}), (\<lambda>p_1. bEx(Value, (\<lambda>w_1. VotedFor(p_1, b, w_1))))), b, x))))" (is "~(\\E x : ?z_hfe(x))")
    have z_Hhv: "~?z_hfe((CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x))))" (is "~(_&?z_hhw)")
    by (rule zenon_notex_0 [of "?z_hfe" "(CHOOSE x:((x \\in Value)&VotedFor((CHOOSE x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))), b, x)))", OF z_Hhu])
    show FALSE
    proof (rule zenon_notand [OF z_Hhv])
     assume z_Hhx:"(~?z_hfb)"
     show FALSE
     by (rule notE [OF z_Hhx z_Hfb])
    next
     assume z_Hhy:"(~?z_hhw)"
     have z_Hhz_z_Hhy: "(~?z_hfc) == (~?z_hhw)" (is "?z_hhz == ?z_hhy")
     by (unfold bChoose_def)
     have z_Hhz: "?z_hhz"
     by (unfold z_Hhz_z_Hhy, fact z_Hhy)
     show FALSE
     by (rule notE [OF z_Hhz z_Hfc])
    qed
   qed
  next
   assume z_Hcv:"(~(\\E x:((x \\in (Acceptor \\ {self}))&bEx(Value, (\<lambda>w_1. VotedFor(x, b, w_1))))))" (is "~(\\E x : ?z_hdd(x))")
   show FALSE
   by (rule zenon_L1_ [OF z_Hcv z_Hd z_Hf z_He])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1199"; *} qed
lemma ob'1210:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition VInv suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'152: "(((fapply (([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))]), (self))) = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))))"
shows "(((<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>) \<in> (fapply (([(votes) EXCEPT ![(self)] = (((fapply ((votes), (self))) \<union> ({(<<(b), (cond((\<exists> p \<in> (((Acceptor) \\ ({(self)}))) : (\<exists> w \<in> (Value) : ((VotedFor ((p), (b), (w)))))), (bChoice((Value), %w. ((VotedFor ((bChoice((((Acceptor) \\ ({(self)}))), %p. (\<exists> w_1 \<in> (Value) : ((VotedFor ((p), (b), (w_1))))))), (b), (w)))))), (bChoice((Value), %v. ((SafeAt ((b), (v))))))))>>)})))]), (self)))))"(is "PROP ?ob'1210")
proof -
ML_command {* writeln "*** TLAPS ENTER 1210"; *}
show "PROP ?ob'1210"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1210"; *} qed
lemma ob'1226:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
fixes self
assumes self_in : "(self \<in> (Q))"
assumes v'125: "(((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a)))"
assumes v'126: "(\<exists> v \<in> (Value) : ((VotedFor ((self), (b), (v)))))"
assumes v'127: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
assumes v'133: "((((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))) \<Longrightarrow> (\<exists> v \<in> (Value) : ((a_hedffe1caafe019043ade750241d505a ((self), (b), (v)) :: c)))))"
assumes v'134: "(Next)"
assumes v'139: "(((TypeOK) \<Rightarrow> (((Next) = (\<exists> self_1 \<in> (Acceptor) : (\<exists> b_1 \<in> (Ballot) : ((BallotAction ((self_1), (b_1))))))))))"
shows "(\<exists> a \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : ((BallotAction ((a), (a_ca))))))"(is "PROP ?ob'1226")
proof -
ML_command {* writeln "*** TLAPS ENTER 1226"; *}
show "PROP ?ob'1226"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_b559c9.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_b559c9.znn.out
;; obligation #1226
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "self_in" (TLA.in self Q)
$hyp "v'125" (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a)
a_VInv4a)
$hyp "v'126" (TLA.bEx Value ((v) (VotedFor self b v)))
$hyp "v'127" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "v'133" (=> (= a_h4fd5f73954dc53af536c1c75068837a
vars) (TLA.bEx Value ((v) (a_hedffe1caafe019043ade750241d505a self b
v))))
$hyp "v'134" Next
$hyp "v'139" (=> TypeOK (= Next
(TLA.bEx Acceptor ((self_1) (TLA.bEx Ballot ((b_1) (BallotAction self_1
b_1)))))))
$goal (TLA.bEx Acceptor ((a) (TLA.bEx Ballot ((a_ca) (BallotAction a
a_ca)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(((TypeOK&a_VInv2a)&a_VInv3a)&a_VInv4a)" (is "?z_hk&_")
 using v'125 by blast
 have z_Hh:"Next"
 using v'134 by blast
 have z_Hi:"(TypeOK=>(Next=bEx(Acceptor, (\<lambda>self_1. bEx(Ballot, (\<lambda>b_1. BallotAction(self_1, b_1)))))))" (is "_=>?z_hq")
 using v'139 by blast
 assume z_Hj:"(~bEx(Acceptor, (\<lambda>self_1. bEx(Ballot, (\<lambda>b_1. BallotAction(self_1, b_1))))))" (is "~?z_hr")
 have z_Hk: "?z_hk" (is "?z_hl&_")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hl: "?z_hl"
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hm: "TypeOK"
 by (rule zenon_and_0 [OF z_Hl])
 have z_Hba_z_Hj: "(~(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))) == (~?z_hr)" (is "?z_hba == ?z_hj")
 by (unfold bEx_def)
 have z_Hba: "?z_hba" (is "~(\\E x : ?z_hbi(x))")
 by (unfold z_Hba_z_Hj, fact z_Hj)
 show FALSE
 proof (rule zenon_imply [OF z_Hi])
  assume z_Hbj:"(~TypeOK)"
  show FALSE
  by (rule notE [OF z_Hbj z_Hm])
 next
  assume z_Hq:"?z_hq"
  have z_Hbk_z_Hq: "(Next=(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))) == ?z_hq" (is "?z_hbk == _")
  by (unfold bEx_def)
  have z_Hbk: "?z_hbk" (is "_=?z_hbb")
  by (unfold z_Hbk_z_Hq, fact z_Hq)
  have z_Hbl: "(TRUE=?z_hbb)" (is "?z_hbm=_")
  by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vja. (zenon_Vja=?z_hbb))" "Next", OF z_Hbk z_Hh])
  have z_Hbb: "?z_hbb"
  by (rule zenon_eq_true_x_0 [of "?z_hbb", OF z_Hbl])
  show FALSE
  by (rule notE [OF z_Hba z_Hbb])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1226"; *} qed
lemma ob'1265:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition vars suppressed *)
(* usable definition ProcSet suppressed *)
(* usable definition Init suppressed *)
(* usable definition acceptor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition chosen suppressed *)
(* usable definition VInv1 suppressed *)
(* usable definition VInv2 suppressed *)
(* usable definition VInv3 suppressed *)
(* usable definition VInv4 suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition BallotAction suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!vars suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!TypeOK suppressed *)
(* usable definition C!Inv suppressed *)
(* usable definition C!SingleCardinalityTest suppressed *)
(* usable definition C!LiveSpec suppressed *)
(* usable definition C!Success suppressed *)
(* usable definition LiveAssumption suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition WellFounded suppressed *)
(* usable definition ProperSubsetRel suppressed *)
fixes Q
assumes Q_in : "(Q \<in> (Quorum))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'119: "(((chosen) \<noteq> ({})))"
assumes v'120: "(((((((Next) \<and> (((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))))) \<and> ((((((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h9c328584958d15e5963012a5e014e1a :: c)))) \<and> ((a_hde69b2e11a77e40b5c91b849e88685a :: c)))) \<and> ((a_hfb87cccee30646b4043b294bd10930a :: c)))))) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
assumes v'123: "((((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))) \<Longrightarrow> ((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) \<noteq> ({})))))"
assumes v'124: "(((((Next) \<and> (((((((TypeOK) \<and> (a_VInv2a))) \<and> (a_VInv3a))) \<and> (a_VInv4a))))) \<and> ((((((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h9c328584958d15e5963012a5e014e1a :: c)))) \<and> ((a_hde69b2e11a77e40b5c91b849e88685a :: c)))) \<and> ((a_hfb87cccee30646b4043b294bd10930a :: c))))))"
assumes v'129: "(((TypeOK) \<Rightarrow> (((Next) = (\<exists> self \<in> (Acceptor) : (\<exists> b_1 \<in> (Ballot) : ((BallotAction ((self), (b_1))))))))))"
shows "(\<exists> self \<in> (Acceptor) : (\<exists> a_ca \<in> (Ballot) : ((BallotAction ((self), (a_ca))))))"(is "PROP ?ob'1265")
proof -
ML_command {* writeln "*** TLAPS ENTER 1265"; *}
show "PROP ?ob'1265"

(* BEGIN ZENON INPUT
;; file=VoteProof.tlaps/tlapm_c97aba.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >VoteProof.tlaps/tlapm_c97aba.znn.out
;; obligation #1265
$hyp "Q_in" (TLA.in Q Quorum)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'119" (-. (= chosen TLA.emptyset))
$hyp "v'120" (\/ (/\ (/\ Next (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a)
a_VInv4a)) (/\ (/\ (/\ a_hef12f5554781c2213604492856f635a
a_h9c328584958d15e5963012a5e014e1a) a_hde69b2e11a77e40b5c91b849e88685a)
a_hfb87cccee30646b4043b294bd10930a)) (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "v'123" (=> (= a_h4fd5f73954dc53af536c1c75068837a
vars) (-. (= h7f4dc7fdc95ffefa185ce3d407a37f
TLA.emptyset)))
$hyp "v'124" (/\ (/\ Next (/\ (/\ (/\ TypeOK a_VInv2a) a_VInv3a) a_VInv4a))
(/\ (/\ (/\ a_hef12f5554781c2213604492856f635a
a_h9c328584958d15e5963012a5e014e1a) a_hde69b2e11a77e40b5c91b849e88685a)
a_hfb87cccee30646b4043b294bd10930a))
$hyp "v'129" (=> TypeOK (= Next
(TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((b_1) (BallotAction self
b_1)))))))
$goal (TLA.bEx Acceptor ((self) (TLA.bEx Ballot ((a_ca) (BallotAction self
a_ca)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"((Next&(((TypeOK&a_VInv2a)&a_VInv3a)&a_VInv4a))&(((a_hef12f5554781c2213604492856f635a&a_h9c328584958d15e5963012a5e014e1a)&a_hde69b2e11a77e40b5c91b849e88685a)&a_hfb87cccee30646b4043b294bd10930a))" (is "?z_hi&?z_hr")
 using v'124 by blast
 have z_Hg:"(TypeOK=>(Next=bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b_1. BallotAction(self, b_1)))))))" (is "_=>?z_hy")
 using v'129 by blast
 assume z_Hh:"(~bEx(Acceptor, (\<lambda>self. bEx(Ballot, (\<lambda>b_1. BallotAction(self, b_1))))))" (is "~?z_hz")
 have z_Hi: "?z_hi" (is "_&?z_hk")
 by (rule zenon_and_0 [OF z_Hf])
 have z_Hj: "Next"
 by (rule zenon_and_0 [OF z_Hi])
 have z_Hk: "?z_hk" (is "?z_hl&_")
 by (rule zenon_and_1 [OF z_Hi])
 have z_Hl: "?z_hl" (is "?z_hm&_")
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hm: "?z_hm"
 by (rule zenon_and_0 [OF z_Hl])
 have z_Hn: "TypeOK"
 by (rule zenon_and_0 [OF z_Hm])
 have z_Hbi_z_Hh: "(~(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))) == (~?z_hz)" (is "?z_hbi == ?z_hh")
 by (unfold bEx_def)
 have z_Hbi: "?z_hbi" (is "~(\\E x : ?z_hbq(x))")
 by (unfold z_Hbi_z_Hh, fact z_Hh)
 show FALSE
 proof (rule zenon_imply [OF z_Hg])
  assume z_Hbr:"(~TypeOK)"
  show FALSE
  by (rule notE [OF z_Hbr z_Hn])
 next
  assume z_Hy:"?z_hy"
  have z_Hbs_z_Hy: "(Next=(\\E x:((x \\in Acceptor)&bEx(Ballot, (\<lambda>b_1. BallotAction(x, b_1)))))) == ?z_hy" (is "?z_hbs == _")
  by (unfold bEx_def)
  have z_Hbs: "?z_hbs" (is "_=?z_hbj")
  by (unfold z_Hbs_z_Hy, fact z_Hy)
  have z_Hbt: "(TRUE=?z_hbj)" (is "?z_hbu=_")
  by (rule zenon_trueistrue_0 [of "(\<lambda>zenon_Vda. (zenon_Vda=?z_hbj))" "Next", OF z_Hbs z_Hj])
  have z_Hbj: "?z_hbj"
  by (rule zenon_eq_true_x_0 [of "?z_hbj", OF z_Hbt])
  show FALSE
  by (rule notE [OF z_Hbi z_Hbj])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1265"; *} qed
end
