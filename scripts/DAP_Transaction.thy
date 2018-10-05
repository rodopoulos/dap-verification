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

  (* Rule modeling the illegal behavior of the Spy *)
  | Fake: "\<lbrakk> evsF \<in> daptrans; X \<in> synth(analz(knows Spy evsF));
             illegalUse(Smartphone A); C \<noteq> Server; C \<noteq> Spy \<rbrakk>
    \<Longrightarrow> Says Spy B X #
        Scans Spy (Smartphone A) X #
        Shows (Smartphone Spy) C X # evsF \<in> daptrans"
  
  (* Reception invariant rules *)
  | Rcpt: "\<lbrakk> evsR \<in> daptrans; Says A B X \<in> set evsR \<rbrakk> 
    \<Longrightarrow> Gets B X # evsR \<in> daptrans"

  | RcptS: "\<lbrakk> evsRs \<in> daptrans; Scans A (Smartphone B) X \<in> set evsRs \<rbrakk> 
    \<Longrightarrow> SGets (Smartphone B) X # evsRs \<in> daptrans"

  | RcptA: "\<lbrakk> evsRa \<in> daptrans; Shows (Smartphone A) B X \<in> set evsRa \<rbrakk>
    \<Longrightarrow> AGets B X # evsRa \<in> daptrans"

  | RcptI: "\<lbrakk> evsRi \<in> daptrans; Inputs A (Smartphone B) X \<in> set evsRi \<rbrakk>
    \<Longrightarrow> SGets (Smartphone B) X # evsRi \<in> daptrans"

  (* Protocol rules *)
  | DT1: "\<lbrakk> evs1 \<in> daptrans; A \<noteq> Server \<rbrakk>
    \<Longrightarrow> Says A Server \<lbrace> Agent A, Number T \<rbrace> # evs1 \<in> daptrans"

  | DT2: "\<lbrakk> evs2 \<in> daptrans; Nonce r \<notin> used evs2;
            Gets Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs2 \<rbrakk>
    \<Longrightarrow> Says Server A \<lbrace> 
          \<lbrace> Agent A, Number T \<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> # evs2 \<in> daptrans"

  | DT3: "\<lbrakk> evs3 \<in> daptrans; legalUse (Smartphone A); A \<noteq> Server;
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
              \<lbrace>Agent A, Number T\<rbrace>,
              Crypt (shrK A) (Nonce r),
              Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
            \<rbrace> \<in> set evs6;
            Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs6;
            SGets (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs6 \<rbrakk>
   \<Longrightarrow> Shows (Smartphone A) A (Nonce r) # evs6 \<in> daptrans"

  | DT7: "\<lbrakk> evs7 \<in> daptrans; A \<noteq> Server;
            Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs7;
            Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs7;
            Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs7;
            Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs7;
            Inputs A (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs7;
            AGets A (Nonce r) \<in> set evs7 \<rbrakk>
    \<Longrightarrow> Says A Server (Nonce r) # evs7 \<in> daptrans"

  | DT8: "\<lbrakk> evs8 \<in> daptrans;
            Gets Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs8;
            Says Server A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r),
              Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
            \<rbrace> \<in> set evs8;
            Gets Server (Nonce r) \<in> set evs8 \<rbrakk>
    \<Longrightarrow> Says Server A Success # evs8 \<in> daptrans"

declare Fake_parts_insert_in_Un [dest]
declare analz_into_parts [dest]





(* GENERAL LEMMAS ON MESSAGE RECEPTION *)

lemma Gets_imp_Says :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> \<exists> A. Says A B X \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma Gets_imp_knows_Spy :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
  
lemma Gets_imp_knows_Spy_analz :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> X \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)

lemma Gets_imp_knows_Spy_analz_Snd :
 "\<lbrakk> Gets B \<lbrace>X, Y\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> Y \<in> analz (knows Spy evs)"

  apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy analz.Inj analz.Snd)
done

lemmas Gets_imp_knows_Spy_parts = Gets_imp_knows_Spy_analz [THEN analz_into_parts]
lemmas Gets_imp_knows_Spy_parts_Snd = Gets_imp_knows_Spy_analz_Snd [THEN analz_into_parts]

lemma SGets_imp_Scans_or_Inputs :
  "\<lbrakk> SGets P X \<in> set evs; evs \<in> daptrans \<rbrakk> 
    \<Longrightarrow> \<exists> A. (Scans A P X \<in> set evs) \<or> (Inputs A P X \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma SGets_imp_knows_Spy :
  "\<lbrakk> SGets (Smartphone B) X \<in> set evs; (Smartphone B) \<in> badP; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> X \<in> knows Spy evs"

  apply (erule rev_mp, erule rev_mp)
  apply (erule daptrans.induct)
  apply (auto)
done

lemma SGets_imp_knows_Spy_analz :
  "\<lbrakk> SGets (Smartphone B) X \<in> set evs; (Smartphone B) \<in> badP; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> X \<in> analz (knows Spy evs)"
by (blast dest!: SGets_imp_knows_Spy)

lemmas SGets_imp_knows_Spy_parts = SGets_imp_knows_Spy_analz [THEN analz_into_parts]

lemma AGets_imp_Shows :
  "\<lbrakk> AGets A X \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> \<exists> P. Shows P A X \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
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

(* 1. General Server guarantees *)

(* Server cannot initiate the protocol *)
lemma Says_Server_DT1_not_evs :
  "evs \<in> daptrans \<Longrightarrow> Says Server Server \<lbrace> Agent Server, Number T \<rbrace> \<notin> set evs"

  apply (erule daptrans.induct)
  apply (simp_all)
done

lemma Server_cannot_initiate :
  "\<lbrakk> Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk> \<Longrightarrow> A \<noteq> Server"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
done


(* - The Server smartphone is not usable *)

lemma Scans_Agent_Server_not_evs [rule_format] :
  "evs \<in> daptrans \<Longrightarrow> Scans Server (Smartphone A) X \<notin> set evs"

  apply (erule daptrans.induct)
  apply (auto)
done

lemma Scans_Server_Agent_not_evs [rule_format] :
  "evs \<in> daptrans \<Longrightarrow> Scans A (Smartphone Server) X \<notin> set evs"

  apply (erule daptrans.induct)
  apply (auto)
done

lemma Shows_Agent_Server_not_evs [rule_format] :
  "evs \<in> daptrans \<Longrightarrow> Shows (Smartphone A) Server X \<notin> set evs"

  apply (erule daptrans.induct)
  apply (simp_all)
done

lemma Shows_Server_Agent_not_evs [rule_format]:
  "evs \<in> daptrans \<Longrightarrow> Shows (Smartphone Server) A X \<notin> set evs"

  apply (erule daptrans.induct)
  apply (simp_all)
done


(* - Server expected message form to the sender *)

lemma Says_Server_DT2 :
  "\<lbrakk> Says Server A \<lbrace> 
       \<lbrace>Agent A, Number T\<rbrace>, 
       Crypt (shrK A) (Nonce r), 
       Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> 
     \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> Gets Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma Says_Server_form_DT2 :
  "\<lbrakk> Says Server A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> r.
         r' = Crypt (shrK A) (Nonce r) \<and>
         h\<^sub>s = Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

(* - The Server only authorizes a transaction if 
     it received a nonce that matches the produced TAN *)

lemma Says_Server_Success :
  "\<lbrakk> Says Server A Success \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> \<exists> T r.
          Gets Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs \<and>
          Says Server A \<lbrace> 
            \<lbrace>Agent A, Number T\<rbrace>, 
            Crypt (shrK A) (Nonce r),
            Crypt (shrK A) \<lbrace>\<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r)\<rbrace>
          \<rbrace> \<in> set evs \<and>
          Gets Server (Nonce r) \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done 




(* 2. General guarantees on smartphones usability *)

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


(* - Legal agents' smartphones firing Scans/Shows must be their owners
     performing a legal action or the Spy performing an illegal action *)

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
        THEN daptrans.DT5, THEN daptrans.RcptI,
        THEN daptrans.DT6, THEN daptrans.RcptA,
        THEN daptrans.DT7, THEN daptrans.Rcpt,
        THEN daptrans.DT8])
  apply (possibility, auto)
done




(* 4. Scans & Inputs events guarantees *)

lemma Scans_A_Smartphone_3 :
  "\<lbrakk> Scans A P \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs \<and>
        Gets A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
done

(* This is an important guarantee: the protocol legally continues if the agent confirms the 
     outputed message, which contains the transaction *)
lemma Inputs_A_Smartphone_5 :
  "\<lbrakk> Inputs A P \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        (\<exists> r' h\<^sub>s. Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs \<and>
        Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs \<and>
        Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs \<and>
        Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done


(* - Message form guarantees *)

lemma Scans_A_Smartphone_form_3 :
  "\<lbrakk> Scans A (Smartphone A) \<lbrace> Transaction, r', h\<^sub>s \<rbrace> \<in> set evs; 
     \<forall> p q. Transaction = \<lbrace>p, q\<rbrace>; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T r. Transaction = \<lbrace> Agent A, Number T \<rbrace>)"
  
  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done

lemma Scans_A_Smartphone_form_DT3:
  "\<lbrakk> Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> \<exists> r. r' = Crypt (shrK A) (Nonce r) \<and>
             h\<^sub>s = Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
  apply (force)
oops



(* 5. Shows events guarantees *) 

(* First, we state that Smartphones provide correct Shows when fed with expected Scans.
   Such lemmas guarantee that Smartphones cannot produce unexpected Shows, preventing the
   Spy from having unlimited resources *)
lemma Shows_A_Smartphone_4 :
  "\<lbrakk> Shows P A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> ((legalUse(P)) \<and> P = (Smartphone A)) \<or> ((illegalUse(P)) \<and> P = (Smartphone Spy)) \<and>
        (\<exists> r. SGets (Smartphone A) \<lbrace>
          \<lbrace>Agent A, Number T\<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
  defer
  apply (blast+)
  apply (auto)
oops

lemma Shows_honest_A_Smartphone_4 :
  "\<lbrakk> Shows P A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        (\<exists> r. SGets (Smartphone A) \<lbrace>
          \<lbrace>Agent A, Number T\<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
  defer
  apply (blast+)
oops

lemma Shows_which_Smartphone_4 :
  "\<lbrakk> Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> r. SGets (Smartphone A) \<lbrace>
          \<lbrace>Agent A, Number T\<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
  defer
  apply (blast+)
done

lemma Shows_A_Smartphone_6 :
  "\<lbrakk> Shows P A (Nonce r) \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T. SGets (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
  defer
  apply (blast+)
oops

lemma Shows_honest_A_Smartphone_6 :
  "\<lbrakk> Shows P A (Nonce r) \<in> set evs; A \<noteq> Spy; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        (\<exists> T. SGets (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
  defer
  apply (blast+)
oops

lemma Shows_which_Smartphone_6 :
  "\<lbrakk> Shows (Smartphone A) A (Nonce r) \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T. SGets (Smartphone A) \<lbrace>Agent A, Number T, Confirmation\<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule daptrans.induct)
  apply (auto)
done



(* - Shows messages form guarantees *)

lemma Shows_A_Smartphone_form_4 :
  "\<lbrakk> Shows (Smartphone A) A Transaction \<in> set evs; \<forall> p q. Transaction = \<lbrace>p, q\<rbrace>;
     evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> \<exists> T. Transaction = \<lbrace>Agent A, Number T\<rbrace>"

  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all)
done

lemma Shows_A_Smartphone_form_6 :
  "\<lbrakk> Shows (Smartphone A) A TAN \<in> set evs; \<forall> p q. TAN \<noteq> \<lbrace>p, q\<rbrace>; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> \<exists> r. TAN = (Nonce r)"

  apply (erule rev_mp, erule rev_mp, erule daptrans.induct)
  apply (simp_all, blast)
done




(* 6. Spy guarantees *)

lemma Spy_knows_Transaction : 
  "\<lbrakk> Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
     \<Longrightarrow> Number T \<in> analz (knows Spy evs)"
by (blast dest!: Says_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd])

lemma Spy_knows_TAN :
  "\<lbrakk> Says A Server (Nonce r) \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> Nonce r \<in> knows Spy evs"
by (blast dest!: Says_imp_knows_Spy)




(* REGULARITY LEMMAS *)

(* For reasoning about encrypted portion of messages *)
lemma DT3_analz_knows_Spy_fst :
 "\<lbrakk> Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> r' \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_Says Gets_imp_knows_Spy_analz_Snd)

lemma DT3_analz_knows_Spy_snd :
 "\<lbrakk> Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> daptrans \<rbrakk>
    \<Longrightarrow> h\<^sub>s \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_Says Gets_imp_knows_Spy_analz_Snd)

lemmas DT3_parts_knows_Spy_fst = DT3_analz_knows_Spy_fst [THEN analz_into_parts]
lemmas DT3_parts_knows_Spy_snd = DT3_analz_knows_Spy_snd [THEN analz_into_parts]

lemma shrK_not_in_honest_Scans [dest]:
  "\<lbrakk>Scans A (Smartphone A) X \<in> set evs; A \<notin> bad; Smartphone P \<notin> badP; evs \<in> daptrans\<rbrakk>
    \<Longrightarrow> Key (shrK A) \<notin> analz {X}"

  apply (erule rev_mp, erule rev_mp, erule rev_mp)
  apply (erule daptrans.induct)
  apply (frule_tac [9] DT3_parts_knows_Spy_fst)
  apply (frule_tac [10] DT3_parts_knows_Spy_snd)
  apply (simp_all, blast)
  apply (auto)
sorry

lemma Spy_parts_keys [simp] : 
  "evs \<in> daptrans \<Longrightarrow> (Key (shrK A) \<in> parts (knows Spy evs)) = (Smartphone A \<in> badP)"

  apply (erule daptrans.induct)
  apply (frule_tac [9] DT3_parts_knows_Spy_fst)
  apply (frule_tac [10] DT3_parts_knows_Spy_snd)
  apply (simp_all)
  apply (auto)
sorry

lemma Spy_analz_shrK [simp] :
  "evs \<in> daptrans \<Longrightarrow> (Key (shrK A) \<in> analz (knows Spy evs)) = (Smartphone A \<in> badP)" 
by (auto dest!: Spy_knows_bad_phones)




(* UNICITY LEMMAS *)

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




(* AUTHENTICITY LEMMAS *)
lemma Checksum_authentic :
  "\<lbrakk> Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> parts (knows Spy evs);
     (Smartphone A) \<notin> badP; evs \<in> daptrans \<rbrakk>
     \<Longrightarrow> r' = Crypt (shrK A) (Nonce r) \<and>
         h\<^sub>s = Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r)\<rbrace> \<and>
         Says Server A \<lbrace>
            \<lbrace>Agent A, Number T\<rbrace>,
            Crypt (shrK A) (Nonce r),
            Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> 
         \<rbrace> \<in> set evs"
      
  apply (erule rev_mp, erule daptrans.induct)
  apply (simp_all (no_asm_simp))
oops

end