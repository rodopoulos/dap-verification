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

axiomatization where
  daptrans_assume_insecure_devices [iff]: "evs \<in> daptrans \<Longrightarrow> insecureP"

inductive_set daptrans :: "event list set" where
  Nil: "[] \<in> daptrans"

  | DT1: "\<lbrakk> evs1 \<in> daptrans; A \<noteq> Server \<rbrakk>
    \<Longrightarrow> Says A Server \<lbrace> Agent A, Number T \<rbrace> # evs1 \<in> daptrans"

  | DT2: "\<lbrakk> evs2 \<in> daptrans;
            Gets Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs2;
            Nonce r \<notin> used evs2 \<rbrakk>
    \<Longrightarrow> Says Server A \<lbrace> 
          \<lbrace> Agent A, Number T \<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> # evs2 \<in> daptrans"

  | DT3: "\<lbrakk> evs3 \<in> daptrans; legalUse (Smartphone A);
            Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs3;
            Gets A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs3 \<rbrakk>
    \<Longrightarrow> Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> # evs3 \<in> daptrans"

  | DT4: "\<lbrakk> evs4 \<in> daptrans; legalUse(Smartphone A); A \<noteq> Server;
            SGets (Smartphone A) \<lbrace>
              \<lbrace>Agent A, Number T\<rbrace>,
              Crypt (shrK A) (Nonce r),
              Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
            \<rbrace> \<in> set evs4 \<rbrakk>
    \<Longrightarrow> Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> # evs4 \<in> daptrans"

  | DT5: "\<lbrakk> evs5 \<in> daptrans; legalUse(Smartphone A);
            Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs5;
            Gets A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs5;
            Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs5;
            Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs5 \<rbrakk>
    \<Longrightarrow> Inputs A (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> # evs5 \<in> daptrans"

  | DT6: "\<lbrakk> evs6 \<in> daptrans; legalUse(Smartphone A); A \<noteq> Server;
            SGets (Smartphone A) \<lbrace>
              \<lbrace> Agent A, Number T \<rbrace>,
              Crypt (shrK A) (Nonce r),
              Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
            \<rbrace> \<in> set evs6;
            Shows (Smartphone A) A \<lbrace> Agent A, Number T \<rbrace> \<in> set evs6;
            Inputs A (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs6 \<rbrakk>
   \<Longrightarrow> Shows (Smartphone A) A (Nonce r) # evs6 \<in> daptrans"

  | DT7: "\<lbrakk> evs7 \<in> daptrans; A \<noteq> Server;
            Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs7;
            Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs7;
            Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs7;
            Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs7;
            Inputs A (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs7;
            AGets A r\<^sub>u \<in> set evs7 \<rbrakk>
    \<Longrightarrow> Says A Server r\<^sub>u # evs7 \<in> daptrans"

  | DT8: "\<lbrakk> evs8 \<in> daptrans;
            Gets Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs8;
            Says Server A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r),
              Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
            \<rbrace> \<in> set evs8;
            Gets Server r\<^sub>u \<in> set evs8;
            r\<^sub>u = Nonce r \<rbrakk>
    \<Longrightarrow> Says Server A Success # evs8 \<in> daptrans"

  (* Rule modeling the illegal behavior of the Spy *)
  | Fake: "\<lbrakk> evsF \<in> daptrans; X \<in> synth(analz(knows Spy evsF));
             illegalUse(Smartphone A); C \<noteq> Server; C \<noteq> Spy \<rbrakk>
    \<Longrightarrow> Says Spy B X #
        Scans Spy (Smartphone A) X #
        Shows (Smartphone Spy) C X # evsF \<in> daptrans"
  
  (* Reception invariant rules *)
  | Rcpt: "\<lbrakk> evsR \<in> daptrans; Says A B X \<in> set evsR \<rbrakk> \<Longrightarrow> Gets B X # evsR \<in> daptrans"

  | RcptS: "\<lbrakk> evsRs \<in> daptrans; Scans A (Smartphone B) X \<in> set evsRs \<rbrakk> 
    \<Longrightarrow> SGets (Smartphone B) X # evsRs \<in> daptrans"

  | RcptA: "\<lbrakk> evsRa \<in> daptrans; Shows (Smartphone A) B X \<in> set evsRa \<rbrakk>
    \<Longrightarrow> AGets B X # evsRa \<in> daptrans"

declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]





(* GENERAL LEMMAS ON MESSAGE RECEPTION *)

lemma Gets_imp_Says :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> \<exists> A. Says A B X \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma Gets_imp_knows_Spy :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> X \<in> analz (knows Spy evs)"

  apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
done

lemma SGets_imp_Scans :
  "\<lbrakk> SGets P X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> \<exists> A. Scans A P X \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma SGets_imp_knows_Spy_badP :
  "\<lbrakk> SGets P X \<in> set evs; P \<in> badP; evs \<in> daptrans \<rbrakk> \<Longrightarrow> X \<in> knows Spy evs"

  apply (erule rev_mp, erule rev_mp, erule daptrans.induct)
  apply (simp_all)
  apply (force dest!: SGets_imp_knows_Spy_insecureP)
done

lemma AGets_imp_Shows :
  "\<lbrakk> AGets A X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> \<exists> P. Shows P A X \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done


lemma Gets_imp_knows_Spy_parts_Snd: 
 "\<lbrakk> Gets B \<lbrace>X, Y\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> Y \<in> parts (knows Spy evs)"

  apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy parts.Inj parts.Snd)
done

lemma Gets_imp_knows_Spy_analz_Snd: 
 "\<lbrakk> Gets B \<lbrace>X, Y\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> Y \<in> analz (knows Spy evs)"

  apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy analz.Inj analz.Snd)
done


(* - Lemmas on insecure devices, from the EventSP.thy, now proved for DAP_Transaction *)
lemma Scans_imp_knows_Spy_insecureP_daptrans :
  "\<lbrakk> Scans Spy P X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> X \<in> knows Spy evs"

  apply (simp (no_asm_simp) add: Scans_imp_knows_Spy)
done

lemma knows_Spy_Scans_insecureP_daptrans_Spy :
  "evs \<in> daptrans \<Longrightarrow> knows Spy (Scans Spy P X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Scans_insecureP_daptrans :
  "\<lbrakk> A \<noteq> Spy; A \<in> bad; evs \<in> daptrans \<rbrakk> 
    \<Longrightarrow> knows Spy (Scans A P X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Shows_insecureM_daptrans_Spy :
  "\<lbrakk> P \<notin> badP; evs \<in> daptrans \<rbrakk> 
    \<Longrightarrow> knows Spy (Shows P Spy X # evs) = knows Spy evs"
by simp

lemma knows_Spy_Shows_insecureM_daptrans :
  "\<lbrakk> P \<in> badP; evs \<in> daptrans \<rbrakk> 
    \<Longrightarrow> knows Spy (Shows P A X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Inputs_daptrans_Spy :
  "evs \<in> daptrans \<Longrightarrow> knows Spy (Inputs Spy P X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Inputs_daptrans :
  "\<lbrakk> A \<noteq> Spy; evs \<in> daptrans \<rbrakk> 
    \<Longrightarrow> knows Spy (Inputs A P X # evs) = knows Spy evs"
by simp



(* RELIABILITY LEMMAS *)

(* 1. Server cannot initiate the protocol *)
lemma Says_Server_DT1_not_evs :
  "evs \<in> daptrans \<Longrightarrow> Says Server Server \<lbrace> Agent Server, Number T \<rbrace> \<notin> set evs"

  apply (erule daptrans.induct)
  apply (simp_all)
done

lemma Server_cannot_initiate :
  "\<lbrakk> evs \<in> daptrans; Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs\<rbrakk> \<Longrightarrow> A \<noteq> Server"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

(* - Also, the Server cannot output something from his smartphone. *)
lemma Shows_Server_not_evs [rule_format]:
  "evs \<in> daptrans \<Longrightarrow> Shows (Smartphone Server) A X \<notin> set evs"

  apply (erule daptrans.induct)
  apply (auto)
done

lemma Shows_Server_not_evs2 [rule_format] :
  "evs \<in> daptrans \<Longrightarrow> Shows (Smartphone A) Server X \<notin> set evs"

  apply (erule daptrans.induct)
  apply (auto)
done

(* - Server expected message form to the sender *)
lemma DT2_Says_Server_message_form :
  "\<lbrakk> Says Server A \<lbrace> Transaction, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T r. Transaction = \<lbrace> Agent A, Number T \<rbrace> \<and> 
         r' = Crypt (shrK A) (Nonce r) \<and>
         h\<^sub>s = Crypt (shrK A) \<lbrace> Transaction, Crypt (shrK A) (Nonce r) \<rbrace>)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

(* - The Server only authorizes a transaction if it received a nonce that matches the produced TAN *)
lemma Says_Server_Success :
  "\<lbrakk> Says Server A Success \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> \<exists> T r r\<^sub>u.
          Gets Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs \<and>
          Says Server A \<lbrace> 
            \<lbrace>Agent A, Number T\<rbrace>, 
            Crypt (shrK A) (Nonce r),
            Crypt (shrK A) \<lbrace>\<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r)\<rbrace>
          \<rbrace> \<in> set evs \<and>
          Gets Server (Nonce r\<^sub>u) \<in> set evs \<and> 
          r = r\<^sub>u"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done 



(* 2. General guarantees for smartphone events *)

(* - Defining legalUse conditions *)
lemma Scans_Smartphone_legalUse :
  "\<lbrakk> Scans A (Smartphone A) X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> legalUse(Smartphone A)"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done

lemma Shows_Smartphone_legalUse :
  "\<lbrakk> Shows (Smartphone A) A X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> legalUse(Smartphone A)"
apply (erule rev_mp, erule daptrans.induct)
apply (auto)
done



(* - Legal agents firing Scans/Shows must performs legal actions from their smartphones or Spy
  performing illegal actions*)
lemma Scans_Smartphone :
  "\<lbrakk> Scans A P X \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (P = (Smartphone A) \<and> legalUse(P)) \<or> (P = (Smartphone Spy) \<and> illegalUse(P))"
  
  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma Shows_Smartphone :
  "\<lbrakk> Shows P A X \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (P = (Smartphone A) \<and> legalUse(P)) \<or> (P = (Smartphone Spy))"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
done

lemma Scans_Shows_Smartphone :
  "\<lbrakk> Scans A P X \<in> set evs \<or> Shows P A X \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
     \<Longrightarrow> (P = (Smartphone A) \<and> legalUse(Smartphone A)) \<or> (P = (Smartphone Spy))"

  apply (blast dest: Scans_Smartphone Shows_Smartphone)
done

(* - The spy can act both legally (using her smartphone) or illegally (using someone else) *)
lemma Scans_Smartphone_Spy :
  "\<lbrakk> Scans Spy P X \<in> set evs \<or> Shows P Spy X \<in> set evs; evs \<in> daptrans \<rbrakk>  
      \<Longrightarrow> (P = (Smartphone Spy)) \<and> (legalUse(Smartphone Spy)) \<or>  
          (\<exists> A. P = (Smartphone A) \<and> illegalUse(Smartphone A))"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done



(* 3. Protocol termination  *)

lemma Protocol_terminates :
  "\<exists> A Success. \<exists> evs \<in> daptrans. A \<noteq> Server \<and> Says Server A Success \<in> set evs"

  apply (intro exI bexI)
  apply (rule_tac [2] daptrans.Nil [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3, THEN daptrans.RcptS,
        THEN daptrans.DT4, THEN daptrans.RcptA,
        THEN daptrans.DT5, (* Here, agent does not need to receive the smartphone output *)
        THEN daptrans.DT6, THEN daptrans.RcptA,
        THEN daptrans.DT7, THEN daptrans.Rcpt,
        THEN daptrans.DT8])
  apply (possibility, auto)
done




(* 4. Scans & Inputs events guarantees *)

lemma Scans_A_Smartphone_3 :
  "\<lbrakk> Scans A P \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        (Gets A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

(* This is an important guarantee: the protocol legally continues if the agent confirms the 
     outputed message, which contains the transaction *)
lemma Inputs_A_Smartphone_5 :
  "\<lbrakk> Inputs A P \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and> Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done


(* - message form guarantees *)

lemma Scans_A_Smartphone_form_3 :
  "\<lbrakk> Scans A (Smartphone A) \<lbrace> Transaction, r', h\<^sub>s \<rbrace> \<in> set evs; 
     \<forall> p q. Transaction = \<lbrace>p, q\<rbrace>; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T r. Transaction = \<lbrace> Agent A, Number T \<rbrace>)"
  
  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done




(* 5. Shows events guarantees *) 

(* First, we state that Smartphones provide correct Shows when fed with expected Scans.
   Such lemmas guarantee that Smartphones cannot produce unexpected Shows, giving the Spy
   unlimited resources *)
lemma Shows_which_Smartphone_4 :
  "\<lbrakk> Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> r. SGets (Smartphone A) \<lbrace>
          \<lbrace>Agent A, Number T\<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma Shows_which_Smartphone_6 :
  "\<lbrakk> Shows (Smartphone A) A (Nonce r) \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T. Inputs A (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done



(* - Shows messages form guarantees *)

lemma Shows_A_Smartphone_form_4 :
  "\<lbrakk> Shows (Smartphone A) A Transaction \<in> set evs; evs \<in> daptrans;
    \<forall> p q. Transaction = \<lbrace>p, q\<rbrace> \<rbrakk>
    \<Longrightarrow> \<exists> T. Transaction = \<lbrace>Agent A, Number T\<rbrace>"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma Shows_A_Smartphone_form_6 :
  "\<lbrakk> Shows (Smartphone A) A TAN \<in> set evs; evs \<in> daptrans;
    \<forall> p q. TAN \<noteq> \<lbrace>p, q\<rbrace> \<rbrakk>
    \<Longrightarrow> \<exists> r. TAN = Nonce r"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma AGets_A_form_7:
  "\<lbrakk> AGets A TAN \<in> set evs; \<forall> p. TAN = p; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> \<exists> r. TAN = Nonce r"
    
  apply (erule rev_mp, erule rev_mp, erule daptrans.induct)
  apply (simp_all)
done




(* 5. Regularity lemmas *)

(* For reasoning about encrypted portion of messages *)
lemma DT3_analz_knows_Spy_fst :
 "\<lbrakk> Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> r' \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_Says Gets_imp_knows_Spy_analz_Snd)

lemma DT3_analz_knows_Spy_snd :
 "\<lbrakk> Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> h\<^sub>s \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_Says Gets_imp_knows_Spy_analz_Snd)

lemma DT7_analz_knows_Spy :
 "\<lbrakk> AGets A r\<^sub>u \<in> set evs; A \<in> bad; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> r\<^sub>u \<in> analz (knows Spy evs)"

  apply (erule rev_mp, erule rev_mp, erule daptrans.induct)
  apply (simp_all)
oops


lemmas DT3_parts_knows_Spy_fst = DT3_analz_knows_Spy_fst [THEN analz_into_parts]
lemmas DT3_parts_knows_Spy_snd = DT3_analz_knows_Spy_snd [THEN analz_into_parts]
lemmas DT7_parts_knows_Spy = DT7_analz_knows_Spy [THEN analz_into_parts]

lemma Spy_parts_keys [simp]: 
  "evs \<in> daptrans \<Longrightarrow> (Key (shrK A) \<in> parts (knows Spy evs)) = (Smartphone A \<in> badP)"

  apply (erule daptrans.induct)
  apply (frule_tac [4] DT3_parts_knows_Spy_fst)
  apply (frule_tac [5] DT3_parts_knows_Spy_snd)
  apply (simp_all, auto)
oops



(* Spy Guarantees *)

lemma Spy_knows_Transaction : 
  "\<lbrakk> Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
     \<Longrightarrow> Number T \<in> analz (knows Spy evs)"
apply (blast dest!: Says_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd])
done




(* 6. Unicity lemmas *)

(* The TAN r uniquely identifies a transaction at the Server side *)
lemma Server_transaction_unique :
  "\<lbrakk> Says Server A \<lbrace> 
      \<lbrace>Agent A, Number T\<rbrace>,
      Crypt (shrK A) (Nonce r),
      Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
    \<rbrace> \<in> set evs ;
    Says Server A' \<lbrace> 
      \<lbrace>Agent A', Number T'\<rbrace>,
      Crypt (shrK A') (Nonce r),
      Crypt (shrK A') \<lbrace> \<lbrace>Agent A', Number T'\<rbrace>, Crypt (shrK A') (Nonce r) \<rbrace>
     \<rbrace> \<in> set evs;
    evs \<in> daptrans\<rbrakk>
   \<Longrightarrow> A = A' \<and> T = T'"

  apply (erule rev_mp, erule rev_mp)
  apply (erule daptrans.induct, simp_all)
  apply (fastforce dest: Says_parts_used)
done


end