(*
  Title: Dynamic Authorization Protocol - Message Transaction
  Author: Felipe Rodopoulos de Oliveira
*)

theory DAP_Transaction imports "./Smartphone"

begin

abbreviation
  Confirmation :: msg where "Confirmation \<equiv> (Number 1)"
abbreviation
  Success :: msg where "Success \<equiv> (Number 2)"

inductive_set daptrans :: "event list set" where
  Nil: "[] \<in> daptrans"

  | DT1: "\<lbrakk> evs1 \<in> daptrans; A \<noteq> Server \<rbrakk>
    \<Longrightarrow> Says A Server \<lbrace> Agent A, Number T \<rbrace> # evs1 \<in> daptrans"

  | DT2: "\<lbrakk> evs2 \<in> daptrans;
          Gets Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs2;
          Nonce r \<notin> used evs2 \<rbrakk>
    \<Longrightarrow> Says Server A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, 
                        Crypt (shrK A) (Nonce r), 
                        Hash \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> \<rbrace> # evs2 \<in> daptrans"

  | DT3: "\<lbrakk> evs3 \<in> daptrans; legalUse (Smartphone A);
            Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs3;
            Gets A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs3 \<rbrakk> 
    \<Longrightarrow> Inputs A (Smartphone A) \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> # evs3 \<in> daptrans"

  | DT4: "\<lbrakk> evs4 \<in> daptrans;
            legalUse(Smartphone A); A \<noteq> Server;
            Gets_s (Smartphone A) \<lbrace> Transaction', r', h\<^sub>s \<rbrace> \<in> set evs4;
            (h\<^sub>s == Hash \<lbrace> Transaction', r' \<rbrace>) \<rbrakk> 
    \<Longrightarrow> Outputs (Smartphone A) A Transaction' # evs4 \<in> daptrans"

  | DT5: "\<lbrakk> evs5 \<in> daptrans; legalUse(Smartphone A);
            Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs5;
            Gets A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs5;
            Inputs A (Smartphone A) \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs5;
            Gets_a A Transaction' \<in> set evs5;
            Transaction' == \<lbrace> Agent A, Number T \<rbrace> \<rbrakk>
    \<Longrightarrow> Inputs A (Smartphone A) Confirmation # evs5 \<in> daptrans"

  | DT6: "\<lbrakk> evs6 \<in> daptrans; A \<noteq> Server; legalUse(Smartphone A);
            Gets_s (Smartphone A) \<lbrace> Transaction', r', h\<^sub>s \<rbrace> \<in> set evs6;
            Outputs (Smartphone A) A Transaction' \<in> set evs6; 
            Gets_s (Smartphone A) Confirmation \<in> set evs6;
            r_u \<notin> used evs6 (* This must go away *) \<rbrakk>
            (* TODO: formalize how r_u is obtained *)
   \<Longrightarrow> Outputs (Smartphone A) A r_u # evs6 \<in> daptrans"

  | DT7: "\<lbrakk> evs7 \<in> daptrans; A \<noteq> Server;
            Says A Server Transaction \<in> set evs7;
            Gets A \<lbrace> Transaction, r', h\<^sub>s \<rbrace> \<in> set evs7;
            Inputs A (Smartphone A) \<lbrace> Transaction, r', h\<^sub>s \<rbrace> \<in> set evs7;
            Gets_a A Transaction' \<in> set evs7;
            Inputs A (Smartphone A) Confirmation \<in> set evs7;
            Gets_a A r_u \<in> set evs7 \<rbrakk>
    \<Longrightarrow> Says A Server r_u # evs7 \<in> daptrans"

  | DT8: "\<lbrakk> evs8 \<in> daptrans;
            Gets Server Transaction \<in> set evs8;
            Says Server A \<lbrace> Transaction, r', h_u \<rbrace> \<in> set evs8;
            Gets Server r_u \<in> set evs8;
            r_u == r' \<rbrakk>
    \<Longrightarrow> Says Server A Success # evs8 \<in> daptrans"

  | Fake: "\<lbrakk> evsF \<in> daptrans; X \<in> synth(analz(knows Spy evsF)); illegalUse(Smartphone B) \<rbrakk> 
    \<Longrightarrow> Says Spy B X # 
        Inputs Spy (Smartphone B) X # evsF \<in> daptrans"
    
  | Rcpt: "\<lbrakk> evsR \<in> daptrans; Says A B X \<in> set evsR \<rbrakk> \<Longrightarrow> Gets B X # evsR \<in> daptrans"

  | Rcpt_s: "\<lbrakk> evsRs \<in> daptrans; Inputs A (Smartphone B) X \<in> set evsRs \<rbrakk> 
    \<Longrightarrow> Gets_s (Smartphone B) X # evsRs \<in> daptrans"

  | Rcpt_a: "\<lbrakk> evsRa \<in> daptrans; Outputs (Smartphone A) B X \<in> set evsRa \<rbrakk>
    \<Longrightarrow> Gets_a B X # evsRa \<in> daptrans"

declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]

(* TECHNICAL LEMMAS *)
lemma Gets_imp_Says :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> \<exists> A. Says A B X \<in> set evs"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

lemma Gets_s_imp_Inputs :
  "\<lbrakk> Gets_s P X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> \<exists> A. Inputs A P X \<in> set evs"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

lemma Gets_a_imp_Outputs :
  "\<lbrakk> Gets_a A X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> \<exists> P. Outputs P A X \<in> set evs"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

(* Conformity of protocol steps *)
lemma Inputs_A_Smartphone_3 :
  "\<lbrakk> Inputs A P \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r, h \<rbrace> \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk> 
    \<Longrightarrow> legalUse(P) \<and> P = (Smartphone A) \<and> 
        (Gets A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r, h \<rbrace> \<in> set evs)"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done



(* RELIABILITY LEMMAS *)
lemma Says_Server_DT1_not_evs :
  "evs \<in> daptrans \<Longrightarrow> Says Server Server \<lbrace> Agent Server, Number T \<rbrace> \<notin> set evs"
apply (erule daptrans.induct)
apply (simp_all)
done

lemma Says_Server_message_form_DT2 :
  "\<lbrakk> evs \<in> daptrans; Says Server A \<lbrace> Transaction, r', Checksum \<rbrace> \<in> set evs \<rbrakk>
    \<Longrightarrow> (\<exists> T. Transaction = \<lbrace> Agent A, Number T \<rbrace>) \<and>
        (\<exists> r. r' = Crypt (shrK A) (Nonce r)) \<and>
        Checksum = Hash \<lbrace> Transaction, r' \<rbrace>"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

(* TODO: ask Claudia how did I manage to do this *)
lemma Server_cannot_initiate :
  "\<lbrakk> evs \<in> daptrans; Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs\<rbrakk> \<Longrightarrow> A \<noteq> Server"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

lemma Outputs_Server_not_evs [rule_format]:
  "evs \<in> daptrans \<Longrightarrow> Outputs (Smartphone Server) A X \<notin> set evs"
apply (erule daptrans.induct)
apply (auto)
done

lemma Outputs_Server_not_evs2 [rule_format] :
  "evs \<in> daptrans \<Longrightarrow> Outputs (Smartphone A) Server X \<notin> set evs"
apply (erule daptrans.induct)
apply (auto)
done


(* GENERAL GUARANTEES FOR INPUTS AND OUPUTS*)

(* Defining legalUse conditions *)
lemma Inputs_Smartphone_legalUse :
  "\<lbrakk> Inputs A (Smartphone A) X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> legalUse(Smartphone A)"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

lemma Outputs_Smartphone_legalUse :
  "\<lbrakk> Outputs (Smartphone A) A X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> legalUse(Smartphone A)"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done


lemma Inputs_Smartphone :
  "\<lbrakk> Inputs A P X \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> P = (Smartphone A) \<and> legalUse(P)"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

lemma Outputs_Smartphone :
  "\<lbrakk> Outputs P A X \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> P = (Smartphone A) \<and> legalUse(P)"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

lemma Inputs_Outputs_Smartphone :
  "\<lbrakk> Inputs A P X \<in> set evs \<or> Outputs P A X \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
     \<Longrightarrow> P = (Smartphone A) \<and> legalUse(Smartphone A)"
apply (blast dest: Inputs_Smartphone Outputs_Smartphone)
done



(* PROTOCOL TERMINATION *)
lemma DT2_happens :
  "\<exists> T r. \<exists>evs \<in> daptrans. 
    Says Server A \<lbrace> \<lbrace> Agent A, Number T\<rbrace>,
      Crypt (shrK A) (Nonce r),
      Hash \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> \<rbrace> \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.DT2)
apply (rule_tac [2] daptrans.Rcpt)
apply (rule_tac [2] daptrans.DT1)
apply (rule_tac [2] daptrans.Nil)
apply (simp_all)
apply (possibility, auto)
oops

lemma DT3_happens:
  "\<exists> T r h. \<exists>evs \<in> daptrans. Inputs A (Smartphone A) \<lbrace> T, r, h \<rbrace> \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.DT3)
apply (rule_tac [2] daptrans.Rcpt)
apply (rule_tac [2] daptrans.DT2)
apply (rule_tac [2] daptrans.Rcpt)
apply (rule_tac [2] daptrans.DT1)
apply (rule_tac [2] daptrans.Nil)
apply (simp_all)
(* apply (rule_tac [2] daptrans.Nil 
        [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3]) *)
apply (possibility, auto)
oops

lemma DT4_happens:
  "\<exists> T. \<exists>evs \<in> daptrans. Outputs (Smartphone A) A T \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.Nil 
        [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3, THEN daptrans.Rcpt_s,
        THEN daptrans.DT4])
apply (possibility, auto)
oops

lemma DT5_happens:
  "\<exists> C. \<exists>evs \<in> daptrans. Inputs A (Smartphone A) C \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.Nil
        [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3, THEN daptrans.Rcpt_s,
        THEN daptrans.DT4, THEN daptrans.Rcpt_a,
        THEN daptrans.DT5])
apply (possibility, auto)
oops

lemma DT6_happens :
  "\<exists> r\<^sub>u. \<exists> evs \<in> daptrans. Outputs (Smartphone A) A r\<^sub>u \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.Nil 
        [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3, THEN daptrans.Rcpt_s,
        THEN daptrans.DT4, THEN daptrans.Rcpt_a,
        THEN daptrans.DT5, THEN daptrans.Rcpt_s,
        THEN daptrans.DT6])
apply (possibility, auto)
oops

lemma DT7_happens :
  "\<exists> r\<^sub>u. \<exists> evs \<in> daptrans. Says A Server r\<^sub>u \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.Nil 
        [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3, THEN daptrans.Rcpt_s,
        THEN daptrans.DT4, THEN daptrans.Rcpt_a,
        THEN daptrans.DT5, THEN daptrans.Rcpt_s,
        THEN daptrans.DT6, THEN daptrans.Rcpt_a,
        THEN daptrans.DT7])
apply (simp_all)
apply (possibility)
apply (auto)
oops

lemma Protocol_terminates :
  "\<exists>Success. \<exists>evs \<in> daptrans. Says Server A Success \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.Nil [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3, THEN daptrans.Rcpt_s,
        THEN daptrans.DT4, THEN daptrans.Rcpt_a,
        THEN daptrans.DT5, THEN daptrans.Rcpt_s,
        THEN daptrans.DT6, THEN daptrans.Rcpt_a,
        THEN daptrans.DT7, THEN daptrans.Rcpt,
        THEN daptrans.DT8])
apply (possibility, auto)
oops



end