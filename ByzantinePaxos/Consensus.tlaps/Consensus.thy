(* automatically generated -- do not edit manually *)
theory Consensus imports Constant Zenon begin
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

lemma ob'19:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes chosen chosen'
(* usable definition vars suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv suppressed *)
(* usable definition SingleCardinalityTest suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition Success suppressed *)
assumes v'37: "(((\<exists>chosenp : (((((chosen) = ({}))) & (\<exists> v \<in> (Value) : (((chosenp) = ({(v)}))))) & ((~ (((<<(chosenp)>>) = (<<(chosen)>>))))))) = (\<exists>chosenp : ((((chosen) = ({}))) & (\<exists> v \<in> (Value) : (((chosenp) = ({(v)}))))))))"
assumes v'38: "(((\<exists>chosenp : ((((chosen) = ({}))) & (\<exists> v \<in> (Value) : (((chosenp) = ({(v)})))))) = (((chosen) = ({})))))"
shows "(((\<exists>chosenp : (((((chosen) = ({}))) & (\<exists> v \<in> (Value) : (((chosenp) = ({(v)}))))) & ((~ (((<<(chosenp)>>) = (<<(chosen)>>))))))) = (((chosen) = ({})))))"(is "PROP ?ob'19")
proof -
ML_command {* writeln "*** TLAPS ENTER 19"; *}
show "PROP ?ob'19"

(* BEGIN ZENON INPUT
;; file=Consensus.tlaps/tlapm_0ec33d.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >Consensus.tlaps/tlapm_0ec33d.znn.out
;; obligation #19
$hyp "v'37" (= (E. ((chosenp) (/\ (/\ (= chosen TLA.emptyset)
(TLA.bEx Value ((v) (= chosenp (TLA.set v))))) (-. (= (TLA.tuple chosenp)
(TLA.tuple chosen)))))) (E. ((chosenp) (/\ (= chosen TLA.emptyset)
(TLA.bEx Value ((v) (= chosenp
(TLA.set v))))))))
$hyp "v'38" (= (E. ((chosenp) (/\ (= chosen TLA.emptyset)
(TLA.bEx Value ((v) (= chosenp (TLA.set v))))))) (= chosen
TLA.emptyset))
$goal (= (E. ((chosenp) (/\ (/\ (= chosen TLA.emptyset)
(TLA.bEx Value ((v) (= chosenp (TLA.set v))))) (-. (= (TLA.tuple chosenp)
(TLA.tuple chosen)))))) (= chosen
TLA.emptyset))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((\\E chosenp:(((chosen={})&bEx(Value, (\<lambda>v. (chosenp={v}))))&(<<chosenp>>~=<<chosen>>)))=(\\E chosenp:((chosen={})&bEx(Value, (\<lambda>v. (chosenp={v}))))))" (is "?z_hd=?z_ht")
 using v'37 by blast
 have z_Hb:"(?z_ht=(chosen={}))" (is "_=?z_hg")
 using v'38 by blast
 assume z_Hc:"(?z_hd~=?z_hg)"
 show FALSE
 proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vh. (zenon_Vh=?z_ht))" "(\<lambda>chosenp. ((?z_hg&bEx(Value, (\<lambda>v. (chosenp={v}))))&(<<chosenp>>~=<<chosen>>)))", OF z_Ha])
  assume z_Hy:"(?z_hd=TRUE)" (is "_=?z_hz")
  assume z_Hba:"(?z_hz=?z_ht)"
  have z_Hd: "?z_hd" (is "\\E x : ?z_hx(x)")
  by (rule zenon_eq_x_true_0 [of "?z_hd", OF z_Hy])
  have z_Ht: "?z_ht" (is "\\E x : ?z_hbb(x)")
  by (rule zenon_eq_true_x_0 [of "?z_ht", OF z_Hba])
  show FALSE
  proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vg. (zenon_Vg=?z_hg))" "?z_hbb", OF z_Hb])
   assume z_Hbf:"(?z_ht=?z_hz)"
   assume z_Hbg:"(?z_hz=?z_hg)"
   show FALSE
   proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hg))" "?z_hx", OF z_Hc])
    assume z_Hy:"(?z_hd=?z_hz)"
    assume z_Hbk:"(?z_hz~=?z_hg)"
    show FALSE
    by (rule notE [OF z_Hbk z_Hbg])
   next
    assume z_Hbl:"(?z_hd=FALSE)" (is "_=?z_hbm")
    assume z_Hbn:"(?z_hbm~=?z_hg)"
    have z_Hbo: "(~?z_hd)"
    by (rule zenon_eq_x_false_0 [of "?z_hd", OF z_Hbl])
    show FALSE
    by (rule notE [OF z_Hbo z_Hd])
   qed
  next
   assume z_Hbp:"(?z_ht=FALSE)" (is "_=?z_hbm")
   assume z_Hbq:"(?z_hbm=?z_hg)"
   have z_Hbr: "(~?z_ht)"
   by (rule zenon_eq_x_false_0 [of "?z_ht", OF z_Hbp])
   show FALSE
   by (rule notE [OF z_Hbr z_Ht])
  qed
 next
  assume z_Hbl:"(?z_hd=FALSE)" (is "_=?z_hbm")
  assume z_Hbs:"(?z_hbm=?z_ht)"
  have z_Hbo: "(~?z_hd)" (is "~(\\E x : ?z_hx(x))")
  by (rule zenon_eq_x_false_0 [of "?z_hd", OF z_Hbl])
  have z_Hbr: "(~?z_ht)" (is "~(\\E x : ?z_hbb(x))")
  by (rule zenon_eq_false_x_0 [of "?z_ht", OF z_Hbs])
  show FALSE
  proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vg. (zenon_Vg=?z_hg))" "?z_hbb", OF z_Hb])
   assume z_Hbf:"(?z_ht=TRUE)" (is "_=?z_hz")
   assume z_Hbg:"(?z_hz=?z_hg)"
   have z_Ht: "?z_ht"
   by (rule zenon_eq_x_true_0 [of "?z_ht", OF z_Hbf])
   show FALSE
   by (rule notE [OF z_Hbr z_Ht])
  next
   assume z_Hbp:"(?z_ht=?z_hbm)"
   assume z_Hbq:"(?z_hbm=?z_hg)"
   show FALSE
   proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hg))" "?z_hx", OF z_Hc])
    assume z_Hy:"(?z_hd=TRUE)" (is "_=?z_hz")
    assume z_Hbk:"(?z_hz~=?z_hg)"
    have z_Hd: "?z_hd"
    by (rule zenon_eq_x_true_0 [of "?z_hd", OF z_Hy])
    show FALSE
    by (rule notE [OF z_Hbo z_Hd])
   next
    assume z_Hbl:"(?z_hd=?z_hbm)"
    assume z_Hbn:"(?z_hbm~=?z_hg)"
    show FALSE
    by (rule notE [OF z_Hbn z_Hbq])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 19"; *} qed
lemma ob'24:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes chosen chosen'
(* usable definition vars suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Inv suppressed *)
(* usable definition SingleCardinalityTest suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition Success suppressed *)
assumes v'37: "((((chosen) \<subseteq> (Value))) & ((IsFiniteSet ((chosen)))))"
assumes v'38: "(((Value) \<noteq> ({})))"
shows "(((\<exists>chosenp : ((((chosen) = ({}))) & (\<exists> v \<in> (Value) : (((chosenp) = ({(v)})))))) = (((chosen) = ({})))))"(is "PROP ?ob'24")
proof -
ML_command {* writeln "*** TLAPS ENTER 24"; *}
show "PROP ?ob'24"

(* BEGIN ZENON INPUT
;; file=Consensus.tlaps/tlapm_57bbd5.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >Consensus.tlaps/tlapm_57bbd5.znn.out
;; obligation #24
$hyp "v'37" (/\ (TLA.subseteq chosen Value)
(IsFiniteSet chosen))
$hyp "v'38" (-. (= Value TLA.emptyset))
$goal (= (E. ((chosenp) (/\ (= chosen TLA.emptyset)
(TLA.bEx Value ((v) (= chosenp (TLA.set v))))))) (= chosen
TLA.emptyset))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"(Value~={})"
 using v'38 by blast
 assume z_Hc:"((\\E chosenp:((chosen={})&bEx(Value, (\<lambda>v. (chosenp={v})))))~=(chosen={}))" (is "?z_hf~=?z_hh")
 show FALSE
 proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hh))" "(\<lambda>chosenp. (?z_hh&bEx(Value, (\<lambda>v. (chosenp={v})))))", OF z_Hc])
  assume z_Ht:"(?z_hf=TRUE)" (is "_=?z_hu")
  assume z_Hv:"(?z_hu~=?z_hh)"
  have z_Hf: "?z_hf" (is "\\E x : ?z_hs(x)")
  by (rule zenon_eq_x_true_0 [of "?z_hf", OF z_Ht])
  have z_Hw: "?z_hs((CHOOSE chosenp:(?z_hh&bEx(Value, (\<lambda>v. (chosenp={v}))))))" (is "_&?z_hy")
  by (rule zenon_ex_choose_0 [of "?z_hs", OF z_Hf])
  have z_Hh: "?z_hh"
  by (rule zenon_and_0 [OF z_Hw])
  have z_Hz: "(chosen~={})"
  by (rule zenon_noteq_true_x_0 [of "?z_hh", OF z_Hv])
  show FALSE
  by (rule notE [OF z_Hz z_Hh])
 next
  assume z_Hba:"(?z_hf=FALSE)" (is "_=?z_hbb")
  assume z_Hbc:"(?z_hbb~=?z_hh)"
  have z_Hbd: "(~?z_hf)" (is "~(\\E x : ?z_hs(x))")
  by (rule zenon_eq_x_false_0 [of "?z_hf", OF z_Hba])
  show FALSE
  proof (rule zenon_boolcase_equal [of "(\<lambda>zenon_Vr. (?z_hbb~=zenon_Vr))" "chosen" "{}", OF z_Hbc])
   assume z_Hbh:"(?z_hh=TRUE)" (is "_=?z_hu")
   assume z_Hbi:"(?z_hbb~=?z_hu)"
   have z_Hh: "?z_hh"
   by (rule zenon_eq_x_true_0 [of "?z_hh", OF z_Hbh])
   have z_Hbj: "(~(\\A zenon_Vh:((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))" (is "~(\\A x : ?z_hbp(x))")
   by (rule zenon_notsetequal_0 [of "Value" "{}", OF z_Hb])
   have z_Hbq: "(\\E zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))" (is "\\E x : ?z_hbs(x)")
   by (rule zenon_notallex_0 [of "?z_hbp", OF z_Hbj])
   have z_Hbt: "?z_hbs((CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {})))))" (is "~(?z_hbv<=>?z_hbw)")
   by (rule zenon_ex_choose_0 [of "?z_hbs", OF z_Hbq])
   show FALSE
   proof (rule zenon_notequiv [OF z_Hbt])
    assume z_Hbx:"(~?z_hbv)"
    assume z_Hbw:"?z_hbw"
    show FALSE
    by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))", OF z_Hbw])
   next
    assume z_Hbv:"?z_hbv"
    assume z_Hby:"(~?z_hbw)"
    have z_Hbz: "~?z_hs({(CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))})" (is "~(_&?z_hcb)")
    by (rule zenon_notex_0 [of "?z_hs" "{(CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))}", OF z_Hbd])
    show FALSE
    proof (rule zenon_notand [OF z_Hbz])
     assume z_Hz:"(chosen~={})"
     show FALSE
     by (rule notE [OF z_Hz z_Hh])
    next
     assume z_Hcc:"(~?z_hcb)"
     have z_Hcd_z_Hcc: "(~(\\E x:((x \\in Value)&({(CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))}={x})))) == (~?z_hcb)" (is "?z_hcd == ?z_hcc")
     by (unfold bEx_def)
     have z_Hcd: "?z_hcd" (is "~(\\E x : ?z_hck(x))")
     by (unfold z_Hcd_z_Hcc, fact z_Hcc)
     have z_Hcl: "~?z_hck((CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {})))))" (is "~(_&?z_hcm)")
     by (rule zenon_notex_0 [of "?z_hck" "(CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))", OF z_Hcd])
     show FALSE
     proof (rule zenon_notand [OF z_Hcl])
      assume z_Hbx:"(~?z_hbv)"
      show FALSE
      by (rule notE [OF z_Hbx z_Hbv])
     next
      assume z_Hcn:"({(CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))}~={(CHOOSE zenon_Vh:(~((zenon_Vh \\in Value)<=>(zenon_Vh \\in {}))))})" (is "?z_hca~=_")
      show FALSE
      by (rule zenon_noteq [OF z_Hcn])
     qed
    qed
   qed
  next
   assume z_Hco:"(?z_hh=?z_hbb)"
   assume z_Hcp:"(?z_hbb~=?z_hbb)"
   show FALSE
   by (rule zenon_eqsym [OF z_Hco z_Hbc])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 24"; *} qed
lemma ob'22:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Value
fixes chosen chosen'
(* usable definition vars suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Inv suppressed *)
(* usable definition SingleCardinalityTest suppressed *)
(* usable definition LiveSpec suppressed *)
(* usable definition Success suppressed *)
assumes v'36: "((((chosen) \<subseteq> (Value))) & ((IsFiniteSet ((chosen)))))"
shows "(((\<exists>chosenp : (((((chosen) = ({}))) & (\<exists> v \<in> (Value) : (((chosenp) = ({(v)}))))) & ((~ (((<<(chosenp)>>) = (<<(chosen)>>))))))) = (\<exists>chosenp : ((((chosen) = ({}))) & (\<exists> v \<in> (Value) : (((chosenp) = ({(v)}))))))))"(is "PROP ?ob'22")
proof -
ML_command {* writeln "*** TLAPS ENTER 22"; *}
show "PROP ?ob'22"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 22"; *} qed
end
