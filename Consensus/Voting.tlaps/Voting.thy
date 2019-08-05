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

lemma ob'32:
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
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteAt suppressed *)
(* usable definition ShowsSafeAt suppressed *)
(* usable definition Init suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ChosenAt suppressed *)
(* usable definition chosen suppressed *)
(* usable definition NoneOtherChoosableAt suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition VotesSafe suppressed *)
(* usable definition OneVote suppressed *)
(* usable definition OneValuePerBallot suppressed *)
assumes v'84: "(((((TypeOK) \<and> (VotesSafe))) \<and> (OneValuePerBallot)))"
assumes v'85: "(((Next) \<or> (((((a_voteshash_primea :: c)) = (votes))) & ((((a_maxBalhash_primea :: c)) = (maxBal))))))"
fixes a
assumes a_in : "(a \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'93: "((((greater ((b), (fapply ((maxBal), (a)))))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (b)]))) & ((((a_voteshash_primea :: c)) = (votes)))) | (\<exists> v \<in> (Value) : ((VoteFor ((a), (b), (v))))))"
fixes a_aunde_1a
assumes a_aunde_1a_in : "(a_aunde_1a \<in> (Acceptor))"
fixes a_bunde_1a
assumes a_bunde_1a_in : "(a_bunde_1a \<in> (Ballot))"
fixes v
assumes v_in : "(v \<in> (Value))"
assumes v'112: "((greater ((b), (fapply ((maxBal), (a))))))"
assumes v'113: "((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (b)])))"
assumes v'114: "((((a_voteshash_primea :: c)) = (votes)))"
assumes v'115: "(\<forall> aa \<in> (Acceptor) : (\<forall> bb \<in> (Ballot) : ((((greater ((fapply ((maxBal), (aa))), (bb)))) \<Rightarrow> ((greater ((fapply (((a_maxBalhash_primea :: c)), (aa))), (bb))))))))"
assumes v'116: "(\<forall> aa \<in> (Acceptor) : (\<forall> bb \<in> (Ballot) : ((((DidNotVoteAt ((aa), (bb)))) \<Rightarrow> ((a_h1902b51376fdd3dbe69d9995bcf047a ((aa), (bb)) :: c))))))"
shows "(\<forall> aa \<in> (Acceptor) : (\<forall> bb \<in> (Ballot) : (((((greater ((fapply ((maxBal), (aa))), (bb)))) & ((DidNotVoteAt ((aa), (bb))))) \<Rightarrow> (((greater ((fapply (((a_maxBalhash_primea :: c)), (aa))), (bb)))) & ((a_h1902b51376fdd3dbe69d9995bcf047a ((aa), (bb)) :: c)))))))"(is "PROP ?ob'32")
proof -
ML_command {* writeln "*** TLAPS ENTER 32"; *}
show "PROP ?ob'32"

(* BEGIN ZENON INPUT
;; file=Voting.tlaps/tlapm_3a42da.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >Voting.tlaps/tlapm_3a42da.znn.out
;; obligation #32
$hyp "v'84" (/\ (/\ TypeOK VotesSafe) OneValuePerBallot)
$hyp "v'85" (\/ Next (/\ (= a_voteshash_primea votes) (= a_maxBalhash_primea
maxBal)))
$hyp "a_in" (TLA.in a Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'93" (\/ (/\ (arith.lt (TLA.fapply maxBal a) b) (= a_maxBalhash_primea
(TLA.except maxBal a b)) (= a_voteshash_primea votes))
(TLA.bEx Value ((v) (VoteFor a b
v))))
$hyp "a_aunde_1a_in" (TLA.in a_aunde_1a Acceptor)
$hyp "a_bunde_1a_in" (TLA.in a_bunde_1a Ballot)
$hyp "v_in" (TLA.in v Value)
$hyp "v'112" (arith.lt (TLA.fapply maxBal a)
b)
$hyp "v'113" (= a_maxBalhash_primea
(TLA.except maxBal a b))
$hyp "v'114" (= a_voteshash_primea
votes)
$hyp "v'115" (TLA.bAll Acceptor ((aa) (TLA.bAll Ballot ((bb) (=> (arith.lt bb
(TLA.fapply maxBal aa)) (arith.lt bb
(TLA.fapply a_maxBalhash_primea aa)))))))
$hyp "v'116" (TLA.bAll Acceptor ((aa) (TLA.bAll Ballot ((bb) (=> (DidNotVoteAt aa
bb) (a_h1902b51376fdd3dbe69d9995bcf047a aa
bb))))))
$goal (TLA.bAll Acceptor ((aa) (TLA.bAll Ballot ((bb) (=> (/\ (arith.lt bb
(TLA.fapply maxBal aa)) (DidNotVoteAt aa bb)) (/\ (arith.lt bb
(TLA.fapply a_maxBalhash_primea aa)) (a_h1902b51376fdd3dbe69d9995bcf047a aa
bb)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hl:"bAll(Acceptor, (\<lambda>aa. bAll(Ballot, (\<lambda>bb. ((bb < (maxBal[aa]))=>(bb < (a_maxBalhash_primea[aa])))))))" (is "?z_hl")
 using v'115 by blast
 have z_Hm:"bAll(Acceptor, (\<lambda>aa. bAll(Ballot, (\<lambda>bb. (DidNotVoteAt(aa, bb)=>a_h1902b51376fdd3dbe69d9995bcf047a(aa, bb))))))" (is "?z_hm")
 using v'116 by blast
 assume z_Hn:"(~bAll(Acceptor, (\<lambda>aa. bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[aa]))&DidNotVoteAt(aa, bb))=>((bb < (a_maxBalhash_primea[aa]))&a_h1902b51376fdd3dbe69d9995bcf047a(aa, bb))))))))" (is "~?z_hbi")
 have z_Hbp_z_Hl: "(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. ((bb < (maxBal[x]))=>(bb < (a_maxBalhash_primea[x]))))))) == ?z_hl" (is "?z_hbp == _")
 by (unfold bAll_def)
 have z_Hbp: "?z_hbp" (is "\\A x : ?z_hca(x)")
 by (unfold z_Hbp_z_Hl, fact z_Hl)
 have z_Hcb_z_Hm: "(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (DidNotVoteAt(x, bb)=>a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))) == ?z_hm" (is "?z_hcb == _")
 by (unfold bAll_def)
 have z_Hcb: "?z_hcb" (is "\\A x : ?z_hci(x)")
 by (unfold z_Hcb_z_Hm, fact z_Hm)
 have z_Hcj_z_Hn: "(~(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))) == (~?z_hbi)" (is "?z_hcj == ?z_hn")
 by (unfold bAll_def)
 have z_Hcj: "?z_hcj" (is "~(\\A x : ?z_hcr(x))")
 by (unfold z_Hcj_z_Hn, fact z_Hn)
 have z_Hcs: "(\\E x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))" (is "\\E x : ?z_hcu(x)")
 by (rule zenon_notallex_0 [of "?z_hcr", OF z_Hcj])
 have z_Hcv: "?z_hcu((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))))" (is "~(?z_hcx=>?z_hcy)")
 by (rule zenon_ex_choose_0 [of "?z_hcu", OF z_Hcs])
 have z_Hcx: "?z_hcx"
 by (rule zenon_notimply_0 [OF z_Hcv])
 have z_Hcz: "(~?z_hcy)"
 by (rule zenon_notimply_1 [OF z_Hcv])
 have z_Hda_z_Hcz: "(~(\\A x:((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))))) == (~?z_hcy)" (is "?z_hda == ?z_hcz")
 by (unfold bAll_def)
 have z_Hda: "?z_hda" (is "~(\\A x : ?z_hdn(x))")
 by (unfold z_Hda_z_Hcz, fact z_Hcz)
 have z_Hdo: "(\\E x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))))))" (is "\\E x : ?z_hdq(x)")
 by (rule zenon_notallex_0 [of "?z_hdn", OF z_Hda])
 have z_Hdr: "?z_hdq((CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))))))" (is "~(?z_hdt=>?z_hdu)")
 by (rule zenon_ex_choose_0 [of "?z_hdq", OF z_Hdo])
 have z_Hdt: "?z_hdt"
 by (rule zenon_notimply_0 [OF z_Hdr])
 have z_Hdv: "(~?z_hdu)" (is "~(?z_hdw=>?z_hdx)")
 by (rule zenon_notimply_1 [OF z_Hdr])
 have z_Hdw: "?z_hdw" (is "?z_hdy&?z_hdz")
 by (rule zenon_notimply_0 [OF z_Hdv])
 have z_Hea: "(~?z_hdx)" (is "~(?z_heb&?z_hec)")
 by (rule zenon_notimply_1 [OF z_Hdv])
 have z_Hdy: "?z_hdy"
 by (rule zenon_and_0 [OF z_Hdw])
 have z_Hdz: "?z_hdz"
 by (rule zenon_and_1 [OF z_Hdw])
 show FALSE
 proof (rule zenon_notand [OF z_Hea])
  assume z_Hed:"(~?z_heb)"
  have z_Hee: "?z_hca((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))))" (is "_=>?z_hef")
  by (rule zenon_all_0 [of "?z_hca" "(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))", OF z_Hbp])
  show FALSE
  proof (rule zenon_imply [OF z_Hee])
   assume z_Heg:"(~?z_hcx)"
   show FALSE
   by (rule notE [OF z_Heg z_Hcx])
  next
   assume z_Hef:"?z_hef"
   have z_Heh_z_Hef: "(\\A x:((x \\in Ballot)=>((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))=>(x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))))) == ?z_hef" (is "?z_heh == _")
   by (unfold bAll_def)
   have z_Heh: "?z_heh" (is "\\A x : ?z_hek(x)")
   by (unfold z_Heh_z_Hef, fact z_Hef)
   have z_Hel: "?z_hek((CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))))))" (is "_=>?z_hem")
   by (rule zenon_all_0 [of "?z_hek" "(CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))))))", OF z_Heh])
   show FALSE
   proof (rule zenon_imply [OF z_Hel])
    assume z_Hen:"(~?z_hdt)"
    show FALSE
    by (rule notE [OF z_Hen z_Hdt])
   next
    assume z_Hem:"?z_hem"
    show FALSE
    proof (rule zenon_imply [OF z_Hem])
     assume z_Heo:"(~?z_hdy)"
     show FALSE
     by (rule notE [OF z_Heo z_Hdy])
    next
     assume z_Heb:"?z_heb"
     show FALSE
     by (rule notE [OF z_Hed z_Heb])
    qed
   qed
  qed
 next
  assume z_Hep:"(~?z_hec)"
  have z_Heq: "?z_hci((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))))" (is "_=>?z_her")
  by (rule zenon_all_0 [of "?z_hci" "(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))", OF z_Hcb])
  show FALSE
  proof (rule zenon_imply [OF z_Heq])
   assume z_Heg:"(~?z_hcx)"
   show FALSE
   by (rule notE [OF z_Heg z_Hcx])
  next
   assume z_Her:"?z_her"
   have z_Hes_z_Her: "(\\A x:((x \\in Ballot)=>(DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)=>a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))) == ?z_her" (is "?z_hes == _")
   by (unfold bAll_def)
   have z_Hes: "?z_hes" (is "\\A x : ?z_hev(x)")
   by (unfold z_Hes_z_Her, fact z_Her)
   have z_Hew: "?z_hev((CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))))))" (is "_=>?z_hex")
   by (rule zenon_all_0 [of "?z_hev" "(CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))))))", OF z_Hes])
   show FALSE
   proof (rule zenon_imply [OF z_Hew])
    assume z_Hen:"(~?z_hdt)"
    show FALSE
    by (rule notE [OF z_Hen z_Hdt])
   next
    assume z_Hex:"?z_hex"
    show FALSE
    proof (rule zenon_imply [OF z_Hex])
     assume z_Hey:"(~?z_hdz)"
     show FALSE
     by (rule notE [OF z_Hey z_Hdz])
    next
     assume z_Hec:"?z_hec"
     show FALSE
     by (rule notE [OF z_Hep z_Hec])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 32"; *} qed
end
