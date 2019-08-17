(* automatically generated -- do not edit manually *)
theory PaxosHistVar imports Constant Zenon begin
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

lemma ob'104:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'59: "(((TypeOK) \<and> (MsgInv)))"
assumes v'60: "(Next)"
fixes b
assumes b_in : "(b \<in> (Nat))"
assumes v'75: "(((~ (\<exists> m \<in> (sent) : (((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((m), (''bal''))) = (b)))))))) & (\<exists> v \<in> (Values) : (\<exists> Q \<in> (Quorums) : (\<exists> S \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''acc''))) = (a))))) & ((\<forall> m \<in> (S) : (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0])))))))) | (\<exists> a_ca \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((\<forall> m \<in> (S) : ((leq ((fapply ((m), (''maxVBal''))), (a_ca))))) & (\<exists> m \<in> (S) : ((((fapply ((m), (''maxVBal''))) = (a_ca))) & (((fapply ((m), (''maxVal''))) = (v)))))))) & ((Send ((((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v))))))))))))"
shows "(\<exists> v \<in> (Values) : (\<exists> Q \<in> (Quorums) : (\<exists> S \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''acc''))) = (a))))) & ((\<forall> m \<in> (S) : (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0])))))))) | (\<exists> a_ca \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((\<forall> m \<in> (S) : ((leq ((fapply ((m), (''maxVBal''))), (a_ca))))) & (\<exists> m \<in> (S) : ((((fapply ((m), (''maxVBal''))) = (a_ca))) & (((fapply ((m), (''maxVal''))) = (v)))))))) & ((Send ((((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v)))))))))))"(is "PROP ?ob'104")
proof -
ML_command {* writeln "*** TLAPS ENTER 104"; *}
show "PROP ?ob'104"

(* BEGIN ZENON INPUT
;; file=PaxosHistVar.tlaps/tlapm_6fb0dd.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >PaxosHistVar.tlaps/tlapm_6fb0dd.znn.out
;; obligation #104
$hyp "v'59" (/\ TypeOK
MsgInv)
$hyp "v'60" Next
$hyp "b_in" (TLA.in b arith.N)
$hyp "v'75" (/\ (-. (TLA.bEx sent ((m) (/\ (= (TLA.fapply m "type") "2a")
(= (TLA.fapply m "bal") b)))))
(TLA.bEx Values ((v) (TLA.bEx Quorums ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf sent ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "acc")
a))))) (\/ (TLA.bAll S ((m) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0))))) (TLA.bEx (arith.intrange 0
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (TLA.bAll S ((m) (arith.le (TLA.fapply m "maxVBal")
a_ca))) (TLA.bEx S ((m) (/\ (= (TLA.fapply m "maxVBal") a_ca)
(= (TLA.fapply m "maxVal") v))))))))
(Send (TLA.record "type" "2a" "bal" b "val" v))))))))))
$goal (TLA.bEx Values ((v) (TLA.bEx Quorums ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf sent ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "acc")
a))))) (\/ (TLA.bAll S ((m) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0))))) (TLA.bEx (arith.intrange 0
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (TLA.bAll S ((m) (arith.le (TLA.fapply m "maxVBal")
a_ca))) (TLA.bEx S ((m) (/\ (= (TLA.fapply m "maxVBal") a_ca)
(= (TLA.fapply m "maxVal") v))))))))
(Send (TLA.record "type" "2a" "bal" b "val" v)))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=b)))))&bEx(Values, (\<lambda>v. bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&((bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=v))))))))&Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))))))))))))" (is "?z_hf&?z_ht")
 using v'75 by blast
 assume z_He:"(~?z_ht)"
 have z_Ht: "?z_ht"
 by (rule zenon_and_1 [OF z_Hd])
 show FALSE
 by (rule notE [OF z_He z_Ht])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 104"; *} qed
lemma ob'96:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
assumes v'57: "(((((sent) \<in> ((SUBSET ((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''maxVBal'' : (((Nat) \<union> ({((minus (((Succ[0])))))}))), ''maxVal'' : (((Values) \<union> ({(None)}))), ''acc'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''val'' : (Values)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))))))) \<and> (\<forall> m \<in> (sent) : ((((((fapply ((m), (''type''))) = (''1b''))) \<Rightarrow> (((((VotedForIn ((fapply ((m), (''acc''))), (fapply ((m), (''maxVal''))), (fapply ((m), (''maxVBal'')))))) \<or> (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0]))))))))) & (\<forall> b \<in> ((isa_peri_peri_a (((arith_add ((fapply ((m), (''maxVBal''))), ((Succ[0]))))), ((arith_add ((fapply ((m), (''bal''))), ((minus (((Succ[0]))))))))))) : ((~ (\<exists> v \<in> (Values) : ((VotedForIn ((fapply ((m), (''acc''))), (v), (b))))))))))) & (((((fapply ((m), (''type''))) = (''2a''))) \<Rightarrow> (((SafeAt ((fapply ((m), (''val''))), (fapply ((m), (''bal'')))))) & (\<forall> a_m2a \<in> (sent) : (((((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((a_m2a) = (m))))))))) & (((((fapply ((m), (''type''))) = (''2b''))) \<Rightarrow> (\<exists> a_m2a \<in> (sent) : ((((fapply ((a_m2a), (''type''))) = (''2a''))) & (((fapply ((a_m2a), (''bal''))) = (fapply ((m), (''bal''))))) & (((fapply ((a_m2a), (''val''))) = (fapply ((m), (''val'')))))))))))))"
assumes v'58: "(Next)"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes v
assumes v_in : "(v \<in> (Values))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))))"
assumes v'83: "((((a_senthash_primea :: c)) = (((sent) \<union> ({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v))))})))))"
assumes v'84: "(\<forall>aa : (\<forall>vv : (\<forall>bb : ((((a_h03062837f0f10c4714e0f53023b1a7a ((aa), (vv), (bb)) :: c)) \<Leftrightarrow> ((VotedForIn ((aa), (vv), (bb)))))))))"
assumes v'85: "(\<forall> m \<in> ((a_senthash_primea :: c)) : (\<forall> ma \<in> ((a_senthash_primea :: c)) : (((((((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((ma), (''type''))) = (''2a''))))) \<and> (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((ma) = (m)))))))"
assumes v'86: "(\<forall> a_m2a \<in> ((a_senthash_primea :: c)) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<Rightarrow> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((fapply ((a_m2a), (''val''))), (fapply ((a_m2a), (''bal'')))) :: c)))))"
assumes v'87: "(\<forall> a_m2a \<in> ((((a_senthash_primea :: c)) \\ (sent))) : (((fapply ((a_m2a), (''type''))) \<noteq> (''1b''))))"
shows "(\<forall> m \<in> ((a_senthash_primea :: c)) : ((((((fapply ((m), (''type''))) = (''1b''))) \<Rightarrow> (((((a_h03062837f0f10c4714e0f53023b1a7a ((fapply ((m), (''acc''))), (fapply ((m), (''maxVal''))), (fapply ((m), (''maxVBal'')))) :: c)) \<or> (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0]))))))))) & (\<forall> b_1 \<in> ((isa_peri_peri_a (((arith_add ((fapply ((m), (''maxVBal''))), ((Succ[0]))))), ((arith_add ((fapply ((m), (''bal''))), ((minus (((Succ[0]))))))))))) : ((~ (\<exists> v_1 \<in> (Values) : ((a_h03062837f0f10c4714e0f53023b1a7a ((fapply ((m), (''acc''))), (v_1), (b_1)) :: c))))))))) & (((((fapply ((m), (''type''))) = (''2a''))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((fapply ((m), (''val''))), (fapply ((m), (''bal'')))) :: c)) & (\<forall> a_m2a \<in> ((a_senthash_primea :: c)) : (((((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((a_m2a) = (m))))))))) & (((((fapply ((m), (''type''))) = (''2b''))) \<Rightarrow> (\<exists> a_m2a \<in> ((a_senthash_primea :: c)) : ((((fapply ((a_m2a), (''type''))) = (''2a''))) & (((fapply ((a_m2a), (''bal''))) = (fapply ((m), (''bal''))))) & (((fapply ((a_m2a), (''val''))) = (fapply ((m), (''val'')))))))))))"(is "PROP ?ob'96")
proof -
ML_command {* writeln "*** TLAPS ENTER 96"; *}
show "PROP ?ob'96"

(* BEGIN ZENON INPUT
;; file=PaxosHistVar.tlaps/tlapm_76f88d.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >PaxosHistVar.tlaps/tlapm_76f88d.znn.out
;; obligation #96
$hyp "v'57" (/\ (TLA.in sent
(TLA.SUBSET (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "maxVBal" (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))) "maxVal" (TLA.cup Values
(TLA.set None)) "acc" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "val" Values))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "val" Values "acc" Acceptors))))
(TLA.bAll sent ((m) (/\ (=> (= (TLA.fapply m "type") "1b")
(/\ (\/ (VotedForIn (TLA.fapply m "acc") (TLA.fapply m "maxVal")
(TLA.fapply m "maxVBal")) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0))))
(TLA.bAll (arith.intrange (arith.add (TLA.fapply m "maxVBal")
(TLA.fapply TLA.Succ 0)) (arith.add (TLA.fapply m "bal")
(arith.minus (TLA.fapply TLA.Succ 0)))) ((b) (-. (TLA.bEx Values ((v) (VotedForIn (TLA.fapply m "acc")
v b)))))))) (=> (= (TLA.fapply m "type") "2a")
(/\ (SafeAt (TLA.fapply m "val") (TLA.fapply m "bal"))
(TLA.bAll sent ((a_m2a) (=> (/\ (= (TLA.fapply a_m2a "type") "2a")
(= (TLA.fapply a_m2a "bal") (TLA.fapply m "bal"))) (= a_m2a m))))))
(=> (= (TLA.fapply m "type") "2b")
(TLA.bEx sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type") "2a")
(= (TLA.fapply a_m2a "bal") (TLA.fapply m "bal")) (= (TLA.fapply a_m2a "val")
(TLA.fapply m "val"))))))))))
$hyp "v'58" Next
$hyp "b_in" (TLA.in b arith.N)
$hyp "v_in" (TLA.in v Values)
$hyp "Q_in" (TLA.in Q Quorums)
$hyp "S_in" (TLA.in S (TLA.SUBSET (TLA.subsetOf sent ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal") b))))))
$hyp "v'83" (= a_senthash_primea (TLA.cup sent
(TLA.set (TLA.record "type" "2a" "bal" b "val" v))))
$hyp "v'84" (A. ((aa) (A. ((vv) (A. ((bb) (<=> (a_h03062837f0f10c4714e0f53023b1a7a aa
vv bb) (VotedForIn aa vv
bb))))))))
$hyp "v'85" (TLA.bAll a_senthash_primea ((m) (TLA.bAll a_senthash_primea ((ma) (=> (/\ (/\ (= (TLA.fapply m "type")
"2a") (= (TLA.fapply ma "type") "2a")) (= (TLA.fapply ma "bal")
(TLA.fapply m "bal"))) (= ma
m))))))
$hyp "v'86" (TLA.bAll a_senthash_primea ((a_m2a) (=> (= (TLA.fapply a_m2a "type")
"2a") (a_hd4a7fa801d94bc2a9c69d39a405ea2a (TLA.fapply a_m2a "val")
(TLA.fapply a_m2a "bal")))))
$hyp "v'87" (TLA.bAll (TLA.setminus a_senthash_primea
sent) ((a_m2a) (-. (= (TLA.fapply a_m2a "type")
"1b"))))
$goal (TLA.bAll a_senthash_primea ((m) (/\ (=> (= (TLA.fapply m "type") "1b")
(/\ (\/ (a_h03062837f0f10c4714e0f53023b1a7a (TLA.fapply m "acc")
(TLA.fapply m "maxVal") (TLA.fapply m "maxVBal")) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0))))
(TLA.bAll (arith.intrange (arith.add (TLA.fapply m "maxVBal")
(TLA.fapply TLA.Succ 0)) (arith.add (TLA.fapply m "bal")
(arith.minus (TLA.fapply TLA.Succ 0)))) ((b_1) (-. (TLA.bEx Values ((v_1) (a_h03062837f0f10c4714e0f53023b1a7a (TLA.fapply m "acc")
v_1 b_1)))))))) (=> (= (TLA.fapply m "type") "2a")
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a (TLA.fapply m "val")
(TLA.fapply m "bal"))
(TLA.bAll a_senthash_primea ((a_m2a) (=> (/\ (= (TLA.fapply a_m2a "type")
"2a") (= (TLA.fapply a_m2a "bal") (TLA.fapply m "bal"))) (= a_m2a m))))))
(=> (= (TLA.fapply m "type") "2b")
(TLA.bEx a_senthash_primea ((a_m2a) (/\ (= (TLA.fapply a_m2a "type") "2a")
(= (TLA.fapply a_m2a "bal") (TLA.fapply m "bal")) (= (TLA.fapply a_m2a "val")
(TLA.fapply m "val")))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}))" (is "_=?z_hn")
 using v'83 by blast
 have z_Hh:"(\\A aa:(\\A vv:(\\A bb:(a_h03062837f0f10c4714e0f53023b1a7a(aa, vv, bb)<=>VotedForIn(aa, vv, bb)))))" (is "\\A x : ?z_hbf(x)")
 using v'84 by blast
 have z_Ha:"((sent \\in SUBSET(((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))&bAll(sent, (\<lambda>m. ((((m[''type''])=''1b'')=>((VotedForIn((m[''acc'']), (m[''maxVal'']), (m[''maxVBal'']))|((m[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((m[''maxVBal'']) + 1), ((m[''bal'']) +  -.(1))), (\<lambda>b. (~bEx(Values, (\<lambda>v. VotedForIn((m[''acc'']), v, b))))))))&((((m[''type''])=''2a'')=>(SafeAt((m[''val'']), (m[''bal'']))&bAll(sent, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(m[''bal''])))=>(a_m2a=m))))))&(((m[''type''])=''2b'')=>bEx(sent, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(m[''bal'']))&((a_m2a[''val''])=(m[''val'']))))))))))))" (is "?z_hbg&?z_hcj")
 using v'57 by blast
 have z_Hi:"bAll(a_senthash_primea, (\<lambda>m. bAll(a_senthash_primea, (\<lambda>ma. (((((m[''type''])=''2a'')&((ma[''type''])=''2a''))&((ma[''bal''])=(m[''bal''])))=>(ma=m))))))" (is "?z_hi")
 using v'85 by blast
 have z_Hj:"bAll(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')=>a_hd4a7fa801d94bc2a9c69d39a405ea2a((a_m2a[''val'']), (a_m2a[''bal''])))))" (is "?z_hj")
 using v'86 by blast
 have z_Hk:"bAll((a_senthash_primea \\ sent), (\<lambda>a_m2a. ((a_m2a[''type''])~=''1b'')))" (is "?z_hk")
 using v'87 by blast
 have zenon_L1_: "(~((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)) \\in ?z_hn)) ==> FALSE" (is "?z_hex ==> FALSE")
 proof -
  assume z_Hex:"?z_hex" (is "~?z_hey")
  have z_Hez: "(~((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}))" (is "~?z_hfa")
  by (rule zenon_notin_cup_1 [of "(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))" "sent" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hex])
  have z_Hfb: "((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))~=(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)))" (is "?z_hq~=_")
  by (rule zenon_notin_addElt_0 [of "?z_hq" "?z_hq" "{}", OF z_Hez])
  show FALSE
  by (rule zenon_noteq [OF z_Hfb])
 qed
 have zenon_L2_: "(((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))[''type''])~=''2a'') ==> FALSE" (is "?z_hfd ==> FALSE")
 proof -
  assume z_Hfd:"?z_hfd" (is "?z_hfe~=?z_hs")
  have z_Hff: "((''type'' \\in DOMAIN((''type'' :> (?z_hs) @@ ''bal'' :> (b) @@ ''val'' :> (v))))&(?z_hfe=?z_hs))" (is "?z_hfg&?z_hfi")
  by ((rule zenon_recfield_1)+, rule zenon_recfield_2b)
  have z_Hfi: "?z_hfi"
  by (rule conjD2 [OF z_Hff])
  have z_Hfj: "(?z_hs~=?z_hs)"
  by (rule subst [where P="(\<lambda>zenon_Vox. (zenon_Vox~=?z_hs))", OF z_Hfi z_Hfd])
  show FALSE
  by (rule zenon_noteq [OF z_Hfj])
 qed
 assume z_Hl:"(~bAll(a_senthash_primea, (\<lambda>m. ((((m[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((m[''acc'']), (m[''maxVal'']), (m[''maxVBal'']))|((m[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((m[''maxVBal'']) + 1), ((m[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((m[''acc'']), v_1, b_1))))))))&((((m[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((m[''val'']), (m[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(m[''bal''])))=>(a_m2a=m))))))&(((m[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(m[''bal'']))&((a_m2a[''val''])=(m[''val'']))))))))))))" (is "~?z_hfn")
 have z_Hcj: "?z_hcj"
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hgj_z_Hcj: "(\\A x:((x \\in sent)=>((((x[''type''])=''1b'')=>((VotedForIn((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b. (~bEx(Values, (\<lambda>v. VotedForIn((x[''acc'']), v, b))))))))&((((x[''type''])=''2a'')=>(SafeAt((x[''val'']), (x[''bal'']))&bAll(sent, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(sent, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))) == ?z_hcj" (is "?z_hgj == _")
 by (unfold bAll_def)
 have z_Hgj: "?z_hgj" (is "\\A x : ?z_hib(x)")
 by (unfold z_Hgj_z_Hcj, fact z_Hcj)
 have z_Hic_z_Hi: "(\\A x:((x \\in a_senthash_primea)=>bAll(a_senthash_primea, (\<lambda>ma. (((((x[''type''])=''2a'')&((ma[''type''])=''2a''))&((ma[''bal''])=(x[''bal''])))=>(ma=x)))))) == ?z_hi" (is "?z_hic == _")
 by (unfold bAll_def)
 have z_Hic: "?z_hic" (is "\\A x : ?z_him(x)")
 by (unfold z_Hic_z_Hi, fact z_Hi)
 have z_Hin_z_Hk: "(\\A x:((x \\in (a_senthash_primea \\ sent))=>((x[''type''])~=''1b''))) == ?z_hk" (is "?z_hin == _")
 by (unfold bAll_def)
 have z_Hin: "?z_hin" (is "\\A x : ?z_hir(x)")
 by (unfold z_Hin_z_Hk, fact z_Hk)
 have z_His_z_Hl: "(~(\\A x:((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) == (~?z_hfn)" (is "?z_his == ?z_hl")
 by (unfold bAll_def)
 have z_His: "?z_his" (is "~(\\A x : ?z_hjn(x))")
 by (unfold z_His_z_Hl, fact z_Hl)
 have z_Hjo: "(\\E x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))" (is "\\E x : ?z_hjq(x)")
 by (rule zenon_notallex_0 [of "?z_hjn", OF z_His])
 have z_Hjr: "?z_hjq((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))" (is "~(?z_hjt=>?z_hju)")
 by (rule zenon_ex_choose_0 [of "?z_hjq", OF z_Hjo])
 have z_Hjt: "?z_hjt"
 by (rule zenon_notimply_0 [OF z_Hjr])
 have z_Hjv: "(~?z_hju)" (is "~(?z_hjw&?z_hjx)")
 by (rule zenon_notimply_1 [OF z_Hjr])
 show FALSE
 proof (rule zenon_notand [OF z_Hjv])
  assume z_Hjy:"(~?z_hjw)" (is "~(?z_hjz=>?z_hka)")
  have z_Hjz: "?z_hjz" (is "?z_hkb=?z_hbr")
  by (rule zenon_notimply_0 [OF z_Hjy])
  have z_Hkc: "(~?z_hka)" (is "~(?z_hkd&?z_hke)")
  by (rule zenon_notimply_1 [OF z_Hjy])
  show FALSE
  proof (rule zenon_notand [OF z_Hkc])
   assume z_Hkf:"(~?z_hkd)" (is "~(?z_hkg|?z_hkh)")
   have z_Hki: "(~?z_hkg)"
   by (rule zenon_notor_0 [OF z_Hkf])
   have z_Hkj: "(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal''])~= -.(1))" (is "?z_hkk~=?z_hbv")
   by (rule zenon_notor_1 [OF z_Hkf])
   have z_Hkl: "?z_hbf(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']))" (is "\\A x : ?z_hkn(x)")
   by (rule zenon_all_0 [of "?z_hbf" "((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc''])", OF z_Hh])
   have z_Hko: "?z_hkn(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVal'']))" (is "\\A x : ?z_hkq(x)")
   by (rule zenon_all_0 [of "?z_hkn" "((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVal''])", OF z_Hkl])
   have z_Hkr: "?z_hkq(?z_hkk)" (is "_<=>?z_hks")
   by (rule zenon_all_0 [of "?z_hkq" "?z_hkk", OF z_Hko])
   show FALSE
   proof (rule zenon_equiv [OF z_Hkr])
    assume z_Hki:"(~?z_hkg)"
    assume z_Hkt:"(~?z_hks)"
    have z_Hku: "?z_hir((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))" (is "?z_hkv=>?z_hkw")
    by (rule zenon_all_0 [of "?z_hir" "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))", OF z_Hin])
    show FALSE
    proof (rule zenon_imply [OF z_Hku])
     assume z_Hkx:"(~?z_hkv)"
     show FALSE
     proof (rule zenon_notin_setminus [of "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))" "a_senthash_primea" "sent", OF z_Hkx])
      assume z_Hky:"(~?z_hjt)"
      show FALSE
      by (rule notE [OF z_Hky z_Hjt])
     next
      assume z_Hkz:"((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in sent)" (is "?z_hkz")
      have z_Hla: "?z_hib((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))" (is "_=>?z_hlb")
      by (rule zenon_all_0 [of "?z_hib" "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])=?z_hbv))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) + ?z_hbv)), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))", OF z_Hgj])
      show FALSE
      proof (rule zenon_imply [OF z_Hla])
       assume z_Hlc:"(~?z_hkz)"
       show FALSE
       by (rule notE [OF z_Hlc z_Hkz])
      next
       assume z_Hlb:"?z_hlb" (is "?z_hld&?z_hle")
       have z_Hld: "?z_hld" (is "_=>?z_hlf")
       by (rule zenon_and_0 [OF z_Hlb])
       show FALSE
       proof (rule zenon_imply [OF z_Hld])
        assume z_Hkw:"?z_hkw"
        show FALSE
        by (rule notE [OF z_Hkw z_Hjz])
       next
        assume z_Hlf:"?z_hlf" (is "?z_hlg&?z_hlh")
        have z_Hlg: "?z_hlg"
        by (rule zenon_and_0 [OF z_Hlf])
        show FALSE
        proof (rule zenon_or [OF z_Hlg])
         assume z_Hks:"?z_hks"
         show FALSE
         by (rule notE [OF z_Hkt z_Hks])
        next
         assume z_Hkh:"?z_hkh"
         show FALSE
         by (rule notE [OF z_Hkj z_Hkh])
        qed
       qed
      qed
     qed
    next
     assume z_Hkw:"?z_hkw"
     show FALSE
     by (rule notE [OF z_Hkw z_Hjz])
    qed
   next
    assume z_Hkg:"?z_hkg"
    assume z_Hks:"?z_hks"
    show FALSE
    by (rule notE [OF z_Hki z_Hkg])
   qed
  next
   assume z_Hli:"(~?z_hke)"
   have z_Hlj_z_Hli: "(~(\\A x:((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x))))))) == (~?z_hke)" (is "?z_hlj == ?z_hli")
   by (unfold bAll_def)
   have z_Hlj: "?z_hlj" (is "~(\\A x : ?z_hlv(x))")
   by (unfold z_Hlj_z_Hli, fact z_Hli)
   have z_Hlw: "(\\E x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x)))))))" (is "\\E x : ?z_hly(x)")
   by (rule zenon_notallex_0 [of "?z_hlv", OF z_Hlj])
   have z_Hlz: "?z_hly((CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x))))))))" (is "~(?z_hmb=>?z_hmc)")
   by (rule zenon_ex_choose_0 [of "?z_hly", OF z_Hlw])
   have z_Hmb: "?z_hmb"
   by (rule zenon_notimply_0 [OF z_Hlz])
   have z_Hmd: "(~?z_hmc)" (is "~~?z_hme")
   by (rule zenon_notimply_1 [OF z_Hlz])
   have z_Hme: "?z_hme"
   by (rule zenon_notnot_0 [OF z_Hmd])
   have z_Hmf_z_Hme: "(\\E x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x)))))))))) == ?z_hme" (is "?z_hmf == _")
   by (unfold bEx_def)
   have z_Hmf: "?z_hmf" (is "\\E x : ?z_hmj(x)")
   by (unfold z_Hmf_z_Hme, fact z_Hme)
   have z_Hmk: "?z_hmj((CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x)))))))))))" (is "?z_hmm&?z_hmn")
   by (rule zenon_ex_choose_0 [of "?z_hmj", OF z_Hmf])
   have z_Hmm: "?z_hmm"
   by (rule zenon_and_0 [OF z_Hmk])
   have z_Hmn: "?z_hmn"
   by (rule zenon_and_1 [OF z_Hmk])
   have z_Hkl: "?z_hbf(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']))" (is "\\A x : ?z_hkn(x)")
   by (rule zenon_all_0 [of "?z_hbf" "((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc''])", OF z_Hh])
   have z_Hmo: "?z_hkn((CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x)))))))))))" (is "\\A x : ?z_hmp(x)")
   by (rule zenon_all_0 [of "?z_hkn" "(CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x))))))))))", OF z_Hkl])
   have z_Hmq: "?z_hmp((CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x))))))))" (is "_<=>?z_hmr")
   by (rule zenon_all_0 [of "?z_hmp" "(CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x)))))))", OF z_Hmo])
   show FALSE
   proof (rule zenon_equiv [OF z_Hmq])
    assume z_Hms:"(~?z_hmn)"
    assume z_Hmt:"(~?z_hmr)"
    show FALSE
    by (rule notE [OF z_Hms z_Hmn])
   next
    assume z_Hmn:"?z_hmn"
    assume z_Hmr:"?z_hmr"
    have z_Hku: "?z_hir((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))" (is "?z_hkv=>?z_hkw")
    by (rule zenon_all_0 [of "?z_hir" "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))", OF z_Hin])
    show FALSE
    proof (rule zenon_imply [OF z_Hku])
     assume z_Hkx:"(~?z_hkv)"
     show FALSE
     proof (rule zenon_notin_setminus [of "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))" "a_senthash_primea" "sent", OF z_Hkx])
      assume z_Hky:"(~?z_hjt)"
      show FALSE
      by (rule notE [OF z_Hky z_Hjt])
     next
      assume z_Hkz:"((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in sent)" (is "?z_hkz")
      have z_Hla: "?z_hib((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))" (is "_=>?z_hlb")
      by (rule zenon_all_0 [of "?z_hib" "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))", OF z_Hgj])
      show FALSE
      proof (rule zenon_imply [OF z_Hla])
       assume z_Hlc:"(~?z_hkz)"
       show FALSE
       by (rule notE [OF z_Hlc z_Hkz])
      next
       assume z_Hlb:"?z_hlb" (is "?z_hld&?z_hle")
       have z_Hld: "?z_hld" (is "_=>?z_hlf")
       by (rule zenon_and_0 [OF z_Hlb])
       show FALSE
       proof (rule zenon_imply [OF z_Hld])
        assume z_Hkw:"?z_hkw"
        show FALSE
        by (rule notE [OF z_Hkw z_Hjz])
       next
        assume z_Hlf:"?z_hlf" (is "?z_hlg&?z_hlh")
        have z_Hlh: "?z_hlh"
        by (rule zenon_and_1 [OF z_Hlf])
        have z_Hmu_z_Hlh: "(\\A x:((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v. VotedForIn(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v, x)))))) == ?z_hlh" (is "?z_hmu == _")
        by (unfold bAll_def)
        have z_Hmu: "?z_hmu" (is "\\A x : ?z_hna(x)")
        by (unfold z_Hmu_z_Hlh, fact z_Hlh)
        have z_Hnb: "?z_hna((CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x))))))))" (is "_=>?z_hnc")
        by (rule zenon_all_0 [of "?z_hna" "(CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x)))))))", OF z_Hmu])
        show FALSE
        proof (rule zenon_imply [OF z_Hnb])
         assume z_Hnd:"(~?z_hmb)"
         show FALSE
         by (rule notE [OF z_Hnd z_Hmb])
        next
         assume z_Hnc:"?z_hnc" (is "~?z_hne")
         have z_Hnf_z_Hnc: "(~(\\E x:((x \\in Values)&VotedForIn(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x))))))))))) == ?z_hnc" (is "?z_hnf == _")
         by (unfold bEx_def)
         have z_Hnf: "?z_hnf" (is "~(\\E x : ?z_hnj(x))")
         by (unfold z_Hnf_z_Hnc, fact z_Hnc)
         have z_Hnk: "~?z_hnj((CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x)))))))))))"
         by (rule zenon_notex_0 [of "?z_hnj" "(CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hbr)=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''acc'']), v_1, x))))))))))", OF z_Hnf])
         show FALSE
         proof (rule zenon_notand [OF z_Hnk])
          assume z_Hnl:"(~?z_hmm)"
          show FALSE
          by (rule notE [OF z_Hnl z_Hmm])
         next
          assume z_Hmt:"(~?z_hmr)"
          show FALSE
          by (rule notE [OF z_Hmt z_Hmr])
         qed
        qed
       qed
      qed
     qed
    next
     assume z_Hkw:"?z_hkw"
     show FALSE
     by (rule notE [OF z_Hkw z_Hjz])
    qed
   qed
  qed
 next
  assume z_Hnm:"(~?z_hjx)" (is "~(?z_hnn&?z_hno)")
  show FALSE
  proof (rule zenon_notand [OF z_Hnm])
   assume z_Hnp:"(~?z_hnn)" (is "~(?z_hnq=>?z_hnr)")
   have z_Hnq: "?z_hnq" (is "?z_hkb=?z_hs")
   by (rule zenon_notimply_0 [OF z_Hnp])
   have z_Hns: "(~?z_hnr)" (is "~(?z_hnt&?z_hnu)")
   by (rule zenon_notimply_1 [OF z_Hnp])
   show FALSE
   proof (rule zenon_notand [OF z_Hns])
    assume z_Hnv:"(~?z_hnt)"
    have z_Hnw: "((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in ?z_hn)" (is "?z_hnw")
    by (rule subst [where P="(\<lambda>zenon_Vrvi. ((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in zenon_Vrvi))", OF z_Hg z_Hjt])
    have z_Hoa: "bAll(?z_hn, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a((a_m2a[''val'']), (a_m2a[''bal''])))))" (is "?z_hoa")
    by (rule subst [where P="(\<lambda>zenon_Vvwi. bAll(zenon_Vvwi, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a((a_m2a[''val'']), (a_m2a[''bal'']))))))", OF z_Hg z_Hj])
    have z_Hoe_z_Hoa: "(\\A x:((x \\in ?z_hn)=>(((x[''type''])=?z_hs)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))))) == ?z_hoa" (is "?z_hoe == _")
    by (unfold bAll_def)
    have z_Hoe: "?z_hoe" (is "\\A x : ?z_hoi(x)")
    by (unfold z_Hoe_z_Hoa, fact z_Hoa)
    have z_Hoj: "?z_hoi((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))" (is "_=>?z_hok")
    by (rule zenon_all_0 [of "?z_hoi" "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))", OF z_Hoe])
    show FALSE
    proof (rule zenon_imply [OF z_Hoj])
     assume z_Hol:"(~?z_hnw)"
     show FALSE
     by (rule notE [OF z_Hol z_Hnw])
    next
     assume z_Hok:"?z_hok"
     show FALSE
     proof (rule zenon_imply [OF z_Hok])
      assume z_Hom:"(?z_hkb~=?z_hs)"
      show FALSE
      by (rule notE [OF z_Hom z_Hnq])
     next
      assume z_Hnt:"?z_hnt"
      show FALSE
      by (rule notE [OF z_Hnv z_Hnt])
     qed
    qed
   next
    assume z_Hon:"(~?z_hnu)"
    have z_Hoo_z_Hon: "(~(\\A x:((x \\in a_senthash_primea)=>((((x[''type''])=?z_hs)&((x[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal''])))=>(x=(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))))))) == (~?z_hnu)" (is "?z_hoo == ?z_hon")
    by (unfold bAll_def)
    have z_Hoo: "?z_hoo" (is "~(\\A x : ?z_hov(x))")
    by (unfold z_Hoo_z_Hon, fact z_Hon)
    have z_How: "(\\E x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hs)&((x[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal''])))=>(x=(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))))))" (is "\\E x : ?z_hoy(x)")
    by (rule zenon_notallex_0 [of "?z_hov", OF z_Hoo])
    have z_Hoz: "?z_hoy((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hs)&((x[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal''])))=>(x=(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))))))))" (is "~(?z_hpb=>?z_hpc)")
    by (rule zenon_ex_choose_0 [of "?z_hoy", OF z_How])
    have z_Hpb: "?z_hpb"
    by (rule zenon_notimply_0 [OF z_Hoz])
    have z_Hpd: "(~?z_hpc)" (is "~(?z_hpe=>?z_hpf)")
    by (rule zenon_notimply_1 [OF z_Hoz])
    have z_Hpe: "?z_hpe" (is "?z_hpg&?z_hph")
    by (rule zenon_notimply_0 [OF z_Hpd])
    have z_Hpi: "((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=?z_hs)&((x[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal''])))=>(x=(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))))))~=(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=?z_hs)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=?z_hs)&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=''2b'')=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=?z_hs)&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))" (is "?z_hpa~=?z_hjs")
    by (rule zenon_notimply_1 [OF z_Hpd])
    have z_Hpg: "?z_hpg" (is "?z_hpj=_")
    by (rule zenon_and_0 [OF z_Hpe])
    have z_Hph: "?z_hph" (is "?z_hpk=?z_hlq")
    by (rule zenon_and_1 [OF z_Hpe])
    have z_Hpl: "?z_him(?z_hpa)" (is "_=>?z_hpm")
    by (rule zenon_all_0 [of "?z_him" "?z_hpa", OF z_Hic])
    show FALSE
    proof (rule zenon_imply [OF z_Hpl])
     assume z_Hpn:"(~?z_hpb)"
     show FALSE
     by (rule notE [OF z_Hpn z_Hpb])
    next
     assume z_Hpm:"?z_hpm"
     have z_Hpo_z_Hpm: "(\\A x:((x \\in a_senthash_primea)=>(((?z_hpg&((x[''type''])=?z_hs))&((x[''bal''])=?z_hpk))=>(x=?z_hpa)))) == ?z_hpm" (is "?z_hpo == _")
     by (unfold bAll_def)
     have z_Hpo: "?z_hpo" (is "\\A x : ?z_hpv(x)")
     by (unfold z_Hpo_z_Hpm, fact z_Hpm)
     have z_Hpw: "?z_hpv(?z_hjs)" (is "_=>?z_hpx")
     by (rule zenon_all_0 [of "?z_hpv" "?z_hjs", OF z_Hpo])
     show FALSE
     proof (rule zenon_imply [OF z_Hpw])
      assume z_Hky:"(~?z_hjt)"
      show FALSE
      by (rule notE [OF z_Hky z_Hjt])
     next
      assume z_Hpx:"?z_hpx" (is "?z_hpy=>?z_hpz")
      show FALSE
      proof (rule zenon_imply [OF z_Hpx])
       assume z_Hqa:"(~?z_hpy)" (is "~(?z_hqb&?z_hqc)")
       show FALSE
       proof (rule zenon_notand [OF z_Hqa])
        assume z_Hqd:"(~?z_hqb)"
        show FALSE
        proof (rule zenon_notand [OF z_Hqd])
         assume z_Hqe:"(?z_hpj~=?z_hs)"
         show FALSE
         by (rule notE [OF z_Hqe z_Hpg])
        next
         assume z_Hom:"(?z_hkb~=?z_hs)"
         show FALSE
         by (rule notE [OF z_Hom z_Hnq])
        qed
       next
        assume z_Hqf:"(?z_hlq~=?z_hpk)"
        show FALSE
        by (rule zenon_eqsym [OF z_Hph z_Hqf])
       qed
      next
       assume z_Hpz:"?z_hpz"
       show FALSE
       by (rule zenon_eqsym [OF z_Hpz z_Hpi])
      qed
     qed
    qed
   qed
  next
   assume z_Hqg:"(~?z_hno)" (is "~(?z_hqh=>?z_hqi)")
   have z_Hqh: "?z_hqh" (is "?z_hkb=?z_hci")
   by (rule zenon_notimply_0 [OF z_Hqg])
   have z_Hqj: "(~?z_hqi)"
   by (rule zenon_notimply_1 [OF z_Hqg])
   have z_Hqk_z_Hqj: "(~(\\E x:((x \\in a_senthash_primea)&(((x[''type''])=''2a'')&(((x[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']))&((x[''val''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''val'']))))))) == (~?z_hqi)" (is "?z_hqk == ?z_hqj")
   by (unfold bEx_def)
   have z_Hqk: "?z_hqk" (is "~(\\E x : ?z_hqr(x))")
   by (unfold z_Hqk_z_Hqj, fact z_Hqj)
   have z_Hqs: "(~bEx(?z_hn, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']))&((a_m2a[''val''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''val''])))))))" (is "~?z_hqt")
   by (rule subst [where P="(\<lambda>zenon_Vxwi. (~bEx(zenon_Vxwi, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']))&((a_m2a[''val''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''val'']))))))))", OF z_Hg z_Hqj])
   have z_Hrd_z_Hqs: "(~(\\E x:((x \\in ?z_hn)&(((x[''type''])=''2a'')&(((x[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']))&((x[''val''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''val'']))))))) == (~?z_hqt)" (is "?z_hrd == ?z_hqs")
   by (unfold bEx_def)
   have z_Hrd: "?z_hrd" (is "~(\\E x : ?z_hrg(x))")
   by (unfold z_Hrd_z_Hqs, fact z_Hqs)
   have z_Hnw: "((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in ?z_hn)" (is "?z_hnw")
   by (rule subst [where P="(\<lambda>zenon_Vrvi. ((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in zenon_Vrvi))", OF z_Hg z_Hjt])
   show FALSE
   proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))" "sent" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hnw])
    assume z_Hkz:"((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in sent)" (is "?z_hkz")
    have z_Hla: "?z_hib((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))))" (is "_=>?z_hlb")
    by (rule zenon_all_0 [of "?z_hib" "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))", OF z_Hgj])
    show FALSE
    proof (rule zenon_imply [OF z_Hla])
     assume z_Hlc:"(~?z_hkz)"
     show FALSE
     by (rule notE [OF z_Hlc z_Hkz])
    next
     assume z_Hlb:"?z_hlb" (is "?z_hld&?z_hle")
     have z_Hle: "?z_hle" (is "?z_hrh&?z_hri")
     by (rule zenon_and_1 [OF z_Hlb])
     have z_Hri: "?z_hri" (is "_=>?z_hrj")
     by (rule zenon_and_1 [OF z_Hle])
     show FALSE
     proof (rule zenon_imply [OF z_Hri])
      assume z_Hrk:"(?z_hkb~=?z_hci)"
      show FALSE
      by (rule notE [OF z_Hrk z_Hqh])
     next
      assume z_Hrj:"?z_hrj"
      have z_Hrl_z_Hrj: "(\\E x:((x \\in sent)&(((x[''type''])=''2a'')&(((x[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']))&((x[''val''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''val''])))))) == ?z_hrj" (is "?z_hrl == _")
      by (unfold bEx_def)
      have z_Hrl: "?z_hrl" (is "\\E x : ?z_hrn(x)")
      by (unfold z_Hrl_z_Hrj, fact z_Hrj)
      have z_Hro: "?z_hrn((CHOOSE x:((x \\in sent)&(((x[''type''])=''2a'')&(((x[''bal''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''bal'']))&((x[''val''])=((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))[''val''])))))))" (is "?z_hrq&?z_hrr")
      by (rule zenon_ex_choose_0 [of "?z_hrn", OF z_Hrl])
      have z_Hrq: "?z_hrq"
      by (rule zenon_and_0 [OF z_Hro])
      have z_Hrr: "?z_hrr" (is "?z_hrs&?z_hrt")
      by (rule zenon_and_1 [OF z_Hro])
      have z_Hrs: "?z_hrs" (is "?z_hru=?z_hs")
      by (rule zenon_and_0 [OF z_Hrr])
      have z_Hrt: "?z_hrt" (is "?z_hrv&?z_hrw")
      by (rule zenon_and_1 [OF z_Hrr])
      have z_Hrv: "?z_hrv" (is "?z_hrx=?z_hlq")
      by (rule zenon_and_0 [OF z_Hrt])
      have z_Hrw: "?z_hrw" (is "?z_hry=?z_hqq")
      by (rule zenon_and_1 [OF z_Hrt])
      have z_Hrz: "~?z_hqr((CHOOSE x:((x \\in sent)&(((x[''type''])=?z_hs)&(((x[''bal''])=?z_hlq)&((x[''val''])=?z_hqq))))))" (is "~(?z_hsa&_)")
      by (rule zenon_notex_0 [of "?z_hqr" "(CHOOSE x:((x \\in sent)&(((x[''type''])=?z_hs)&(((x[''bal''])=?z_hlq)&((x[''val''])=?z_hqq)))))", OF z_Hqk])
      show FALSE
      proof (rule zenon_notand [OF z_Hrz])
       assume z_Hsb:"(~?z_hsa)"
       have z_Hsc: "(~((CHOOSE x:((x \\in sent)&(((x[''type''])=?z_hs)&(((x[''bal''])=?z_hlq)&((x[''val''])=?z_hqq))))) \\in ?z_hn))" (is "~?z_hsd")
       by (rule subst [where P="(\<lambda>zenon_Vbxi. (~((CHOOSE x:((x \\in sent)&(((x[''type''])=?z_hs)&(((x[''bal''])=?z_hlq)&((x[''val''])=?z_hqq))))) \\in zenon_Vbxi)))", OF z_Hg z_Hsb])
       have z_Hsi: "(~?z_hrq)"
       by (rule zenon_notin_cup_0 [of "(CHOOSE x:((x \\in sent)&(((x[''type''])=?z_hs)&(((x[''bal''])=?z_hlq)&((x[''val''])=?z_hqq)))))" "sent" "{(''type'' :> (?z_hs) @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hsc])
       show FALSE
       by (rule notE [OF z_Hsi z_Hrq])
      next
       assume z_Hsj:"(~?z_hrr)"
       show FALSE
       proof (rule zenon_notand [OF z_Hsj])
        assume z_Hsk:"(?z_hru~=?z_hs)"
        show FALSE
        by (rule notE [OF z_Hsk z_Hrs])
       next
        assume z_Hsl:"(~?z_hrt)"
        show FALSE
        proof (rule zenon_notand [OF z_Hsl])
         assume z_Hsm:"(?z_hrx~=?z_hlq)"
         show FALSE
         by (rule notE [OF z_Hsm z_Hrv])
        next
         assume z_Hsn:"(?z_hry~=?z_hqq)"
         show FALSE
         by (rule notE [OF z_Hsn z_Hrw])
        qed
       qed
      qed
     qed
    qed
   next
    assume z_Hso:"((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hso")
    show FALSE
    proof (rule zenon_in_addElt [of "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))" "(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))" "{}", OF z_Hso])
     assume z_Hsp:"((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))=(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)))" (is "?z_hjs=?z_hq")
     have z_Hsq: "~?z_hrg(?z_hq)" (is "~(?z_hey&?z_hsr)")
     by (rule zenon_notex_0 [of "?z_hrg" "?z_hq", OF z_Hrd])
     show FALSE
     proof (rule zenon_notand [OF z_Hsq])
      assume z_Hex:"(~?z_hey)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hex])
     next
      assume z_Hss:"(~?z_hsr)" (is "~(?z_hfi&?z_hst)")
      show FALSE
      proof (rule zenon_notand [OF z_Hss])
       assume z_Hfd:"((?z_hq[''type''])~=''2a'')" (is "?z_hfe~=?z_hs")
       show FALSE
       by (rule zenon_L2_ [OF z_Hfd])
      next
       assume z_Hsu:"(~?z_hst)" (is "~(?z_hsv&?z_hsw)")
       show FALSE
       proof (rule zenon_notand [OF z_Hsu])
        assume z_Hsx:"((?z_hq[''bal''])~=(?z_hjs[''bal'']))" (is "?z_hsy~=?z_hlq")
        show FALSE
        proof (rule zenon_noteq [of "?z_hlq"])
         have z_Hsz: "(?z_hq=?z_hjs)"
         by (rule sym [OF z_Hsp])
         have z_Hta: "(?z_hlq~=?z_hlq)"
         by (rule subst [where P="(\<lambda>zenon_Vcxi. ((zenon_Vcxi[''bal''])~=?z_hlq))", OF z_Hsz], fact z_Hsx)
         thus "(?z_hlq~=?z_hlq)" .
        qed
       next
        assume z_Htf:"((?z_hq[''val''])~=(?z_hjs[''val'']))" (is "?z_htg~=?z_hqq")
        show FALSE
        proof (rule zenon_noteq [of "?z_hqq"])
         have z_Hsz: "(?z_hq=?z_hjs)"
         by (rule sym [OF z_Hsp])
         have z_Hth: "(?z_hqq~=?z_hqq)"
         by (rule subst [where P="(\<lambda>zenon_Vdxi. ((zenon_Vdxi[''val''])~=?z_hqq))", OF z_Hsz], fact z_Htf)
         thus "(?z_hqq~=?z_hqq)" .
        qed
       qed
      qed
     qed
    next
     assume z_Htm:"((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val''])))))))))))) \\in {})" (is "?z_htm")
     show FALSE
     by (rule zenon_in_emptyset [of "(CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''1b'')=>((a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))|((x[''maxVBal''])= -.(1)))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>b_1. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, b_1))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(x[''bal''])))=>(a_m2a=x))))))&(((x[''type''])=?z_hci)=>bEx(a_senthash_primea, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&(((a_m2a[''bal''])=(x[''bal'']))&((a_m2a[''val''])=(x[''val'']))))))))))))", OF z_Htm])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 96"; *} qed
lemma ob'110:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
assumes v'59: "(((TypeOK) \<and> (\<forall> m \<in> (sent) : ((((((fapply ((m), (''type''))) = (''1b''))) \<Rightarrow> (((((VotedForIn ((fapply ((m), (''acc''))), (fapply ((m), (''maxVal''))), (fapply ((m), (''maxVBal'')))))) \<or> (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0]))))))))) & (\<forall> b \<in> ((isa_peri_peri_a (((arith_add ((fapply ((m), (''maxVBal''))), ((Succ[0]))))), ((arith_add ((fapply ((m), (''bal''))), ((minus (((Succ[0]))))))))))) : ((~ (\<exists> v \<in> (Values) : ((VotedForIn ((fapply ((m), (''acc''))), (v), (b))))))))))) & (((((fapply ((m), (''type''))) = (''2a''))) \<Rightarrow> (((SafeAt ((fapply ((m), (''val''))), (fapply ((m), (''bal'')))))) & (\<forall> a_m2a \<in> (sent) : (((((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((a_m2a) = (m))))))))) & (((((fapply ((m), (''type''))) = (''2b''))) \<Rightarrow> (\<exists> a_m2a \<in> (sent) : ((((fapply ((a_m2a), (''type''))) = (''2a''))) & (((fapply ((a_m2a), (''bal''))) = (fapply ((m), (''bal''))))) & (((fapply ((a_m2a), (''val''))) = (fapply ((m), (''val'')))))))))))))"
assumes v'60: "(Next)"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes v
assumes v_in : "(v \<in> (Values))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))))"
assumes v'84: "((~ (\<exists> m \<in> (sent) : (((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))"
assumes v'85: "((((a_senthash_primea :: c)) = (((sent) \<union> ({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v))))})))))"
shows "(\<forall> m \<in> ((a_senthash_primea :: c)) : (\<forall> ma \<in> ((a_senthash_primea :: c)) : (((((((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((ma), (''type''))) = (''2a''))))) \<and> (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((ma) = (m)))))))"(is "PROP ?ob'110")
proof -
ML_command {* writeln "*** TLAPS ENTER 110"; *}
show "PROP ?ob'110"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 110"; *} qed
end
