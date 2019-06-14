(*
  Title: Dynamic Authorization Protocol - Message Transaction with Secure Devices
  Author: Felipe Rodopoulos de Oliveira
*)

theory SDAP_Transaction imports "./Smartphone"

begin

axiomatization where
  sdaptrans_assume_insecure_devices [iff]: "evs \<in> sdaptrans \<Longrightarrow> secureP"

inductive_set sdaptrans :: "event list set" where
  Nil: "[] \<in> sdaptrans"

  | DT1: "\<lbrakk> evs1 \<in> sdaptrans; A \<noteq> Server \<rbrakk>
    \<Longrightarrow> Says A Server \<lbrace> Agent A, Number T \<rbrace> # evs1 \<in> sdaptrans"

  | DT2: "\<lbrakk> evs2 \<in> sdaptrans; Nonce r \<notin> used evs2;
            Gets Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs2 \<rbrakk>
    \<Longrightarrow> Says Server A \<lbrace> 
          \<lbrace>Agent A, Number T\<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> # evs2 \<in> sdaptrans"

  | DT3: "\<lbrakk> evs3 \<in> sdaptrans; legalUse (Smartphone A);
            Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs3;
            Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs3 \<rbrakk>
    \<Longrightarrow> Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> # evs3 \<in> sdaptrans"

  | DT4: "\<lbrakk> evs4 \<in> sdaptrans; legalUse(Smartphone A);
            Scans A (Smartphone A) \<lbrace>
              \<lbrace>Agent A, Number T\<rbrace>,
              Crypt (shrK A) (Nonce r),
              Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
            \<rbrace> \<in> set evs4 \<rbrakk>
    \<Longrightarrow> Shows (Smartphone A) A \<lbrace> Agent A, Number T \<rbrace> # evs4 \<in> sdaptrans"

  | DT4_Fake: "\<lbrakk> evs4f \<in> sdaptrans; illegalUse(Smartphone A);
                 Scans Spy (Smartphone A) \<lbrace>
                  \<lbrace>Agent A, Number T\<rbrace>,
                  Crypt (shrK A) (Nonce r),
                  Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
                 \<rbrace> \<in> set evs4f\<rbrakk>
     \<Longrightarrow> Shows (Smartphone A) Spy \<lbrace> Agent A, Number T \<rbrace> # evs4f \<in> sdaptrans"

  (* Agent is confirming the transaction *)
  | DT5: "\<lbrakk> evs5 \<in> sdaptrans; legalUse(Smartphone A);
            Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs5;
            Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs5;
            Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs5;
            Shows (Smartphone A) A \<lbrace> Agent A, Number T \<rbrace> \<in> set evs5 \<rbrakk>
    \<Longrightarrow> Inputs A (Smartphone A) \<lbrace> Agent A, Number T \<rbrace> # evs5 \<in> sdaptrans"

  | DT6: "\<lbrakk> evs6 \<in> sdaptrans; legalUse(Smartphone A);
            Scans A (Smartphone A) \<lbrace>
              \<lbrace>Agent A, Number T\<rbrace>,
              Crypt (shrK A) (Nonce r),
              Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
            \<rbrace> \<in> set evs6;
            Shows (Smartphone A) A \<lbrace> Agent A, Number T \<rbrace> \<in> set evs6;
            Inputs A (Smartphone A) \<lbrace> Agent A, Number T \<rbrace> \<in> set evs6 \<rbrakk>
   \<Longrightarrow> Shows (Smartphone A) A (Nonce r) # evs6 \<in> sdaptrans"

   | DT6_Fake: "\<lbrakk> evs6f \<in> sdaptrans; illegalUse(Smartphone A);
                  Scans Spy (Smartphone A) \<lbrace>
                    \<lbrace>Agent A, Number T\<rbrace>,
                    Crypt (shrK A) (Nonce r),
                    Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
                  \<rbrace> \<in> set evs6f;
                  Shows (Smartphone A) Spy \<lbrace> Agent A, Number T \<rbrace> \<in> set evs6f;
                  Inputs Spy (Smartphone A) \<lbrace> Agent A, Number T \<rbrace> \<in> set evs6f
                \<rbrakk> 
    \<Longrightarrow> Shows (Smartphone A) Spy (Nonce r) # evs6f \<in> sdaptrans"

  | DT7: "\<lbrakk> evs7 \<in> sdaptrans;
            Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs7;
            Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs7;
            Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs7;
            Shows (Smartphone A) A \<lbrace> Agent A, Number T \<rbrace> \<in> set evs7;
            Inputs A (Smartphone A) \<lbrace> Agent A, Number T \<rbrace> \<in> set evs7;
            Shows (Smartphone A) A (Nonce r) \<in> set evs7 \<rbrakk>
    \<Longrightarrow> Says A Server (Nonce r) # evs7 \<in> sdaptrans"

  | DT8: "\<lbrakk> evs8 \<in> sdaptrans; A \<noteq> Server;
            Gets Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs8;
            Says Server A \<lbrace>
              \<lbrace>Agent A, Number T\<rbrace>,
              Crypt (shrK A) (Nonce r),
              Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
            \<rbrace> \<in> set evs8;
            Gets Server (Nonce r) \<in> set evs8 \<rbrakk>
    \<Longrightarrow> Says Server A \<lbrace> Agent A, Number T \<rbrace>  # evs8 \<in> sdaptrans"

  (* Rule modeling the illegal behavior of the Spy *)
  | Fake: "\<lbrakk> evsF \<in> sdaptrans; X \<in> synth(analz(knows Spy evsF));
             illegalUse(Smartphone A); C \<noteq> Server; C \<noteq> Spy \<rbrakk>
    \<Longrightarrow> Says Spy B X #
        Scans Spy (Smartphone A) X # evsF \<in> sdaptrans"
  
  (* Reception invariant rules *)
  | Rcpt: "\<lbrakk> evsR \<in> sdaptrans; Says A B X \<in> set evsR \<rbrakk> \<Longrightarrow> Gets B X # evsR \<in> sdaptrans"


declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]




(* GENERAL LEMMAS ON MESSAGE RECEPTION *)

lemma Gets_imp_Says :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> \<exists> A. Says A B X \<in> set evs"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done

lemma Gets_imp_knows_Spy :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
  
lemma Gets_imp_knows_Spy_analz :
  "\<lbrakk> Gets B X \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> X \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)

lemma Gets_imp_knows_Spy_analz_Snd :
 "\<lbrakk> Gets B \<lbrace>X, Y\<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> Y \<in> analz (knows Spy evs)"

  apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy analz.Inj analz.Snd)
done

lemmas Gets_imp_knows_Spy_parts [dest] = Gets_imp_knows_Spy_analz [THEN analz_into_parts]
lemmas Gets_imp_knows_Spy_parts_Snd [dest] = Gets_imp_knows_Spy_analz_Snd [THEN analz_into_parts]

lemma SGets_imp_Scans :
  "\<lbrakk> SGets P X \<in> set evs; evs \<in> sdaptrans \<rbrakk> 
    \<Longrightarrow> \<exists> A. (Scans A P X \<in> set evs) \<or> (Inputs A P X \<in> set evs)"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done

lemma SGets_imp_knows_Spy :
  "\<lbrakk> SGets (Smartphone B) X \<in> set evs; (Smartphone B) \<in> badP; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> X \<in> knows Spy evs"

  apply (erule rev_mp, erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (auto)
done

lemma SGets_imp_knows_Spy_analz :
  "\<lbrakk> SGets (Smartphone B) X \<in> set evs; (Smartphone B) \<in> badP; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> X \<in> analz (knows Spy evs)"
by (blast dest!: SGets_imp_knows_Spy)

lemmas SGets_imp_knows_Spy_parts [dest] = SGets_imp_knows_Spy_analz [THEN analz_into_parts]

lemma AGets_imp_Shows :
  "\<lbrakk> AGets A X \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> \<exists> P. Shows P A X \<in> set evs"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done


(* - Lemmas on insecure devices, from the EventSP.thy, now proved for DAP_Transaction *)

lemma Scans_imp_knows_Spy_insecureP_sdaptrans :
  "\<lbrakk> Scans Spy P X \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> X \<in> knows Spy evs"

  apply (simp (no_asm_simp) add: Scans_imp_knows_Spy)
done

lemma knows_Spy_Scans_insecureP_sdaptrans_Spy :
  "evs \<in> sdaptrans \<Longrightarrow> knows Spy (Scans Spy P X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Scans_insecureP_sdaptrans :
  "\<lbrakk> A \<noteq> Spy; A \<in> bad; evs \<in> sdaptrans \<rbrakk> 
    \<Longrightarrow> knows Spy (Scans A P X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Shows_secureM_sdaptrans_Spy :
  "evs \<in> sdaptrans \<Longrightarrow> knows Spy (Shows P Spy X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Shows_secureP_sdaptrans :
  "\<lbrakk> P \<in> stolen; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> knows Spy (Shows P Spy X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Inputs_sdaptrans_Spy :
  "evs \<in> sdaptrans \<Longrightarrow> knows Spy (Inputs Spy P X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Inputs_sdaptrans :
  "\<lbrakk> A \<noteq> Spy; evs \<in> sdaptrans \<rbrakk> 
    \<Longrightarrow> knows Spy (Inputs A P X # evs) = knows Spy evs"
by simp



(* For reasoning about encrypted portion of messages *)
lemma DT3_analz_knows_Spy_fst :
 "\<lbrakk> Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> r' \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_Says Gets_imp_knows_Spy_analz_Snd)

lemma DT3_analz_knows_Spy_snd :
 "\<lbrakk> Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> h\<^sub>s \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_Says Gets_imp_knows_Spy_analz_Snd)

lemmas DT3_parts_knows_Spy_fst = DT3_analz_knows_Spy_fst [THEN analz_into_parts]
lemmas DT3_parts_knows_Spy_snd = DT3_analz_knows_Spy_snd [THEN analz_into_parts]


(* == RELIABILITY LEMMAS == *)

(* SERVER GUARANTEES *)

(* Server cannot initiate the protocol *)
lemma Says_Server_DT1_not_evs :
  "evs \<in> sdaptrans \<Longrightarrow> Says Server Server \<lbrace> Agent Server, Number T \<rbrace> \<notin> set evs"

  apply (erule sdaptrans.induct)
  apply (simp_all)
done

lemma Server_cannot_initiate :
  "\<lbrakk> Says A Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> A \<noteq> Server"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (simp_all)
done


(* - The Server smartphone is not usable *)

lemma Scans_Agent_Server_not_evs [rule_format, simp] :
  "evs \<in> sdaptrans \<Longrightarrow> Scans Server (Smartphone A) X \<notin> set evs"

  apply (erule sdaptrans.induct)
  apply (simp_all)
  apply (blast dest:Server_cannot_initiate)
done

lemma Scans_Server_Agent_not_evs [rule_format] :
  "evs \<in> sdaptrans \<Longrightarrow> Scans A (Smartphone Server) X \<notin> set evs"

  apply (erule sdaptrans.induct)
  apply (simp_all)
  apply (blast dest:Server_cannot_initiate)+
done

lemma Shows_Agent_Server_not_evs [rule_format] :
  "evs \<in> sdaptrans \<Longrightarrow> Shows (Smartphone A) Server X \<notin> set evs"

  apply (erule sdaptrans.induct)
  apply (simp_all)
  apply (blast dest:Scans_Server_Agent_not_evs)+
done

lemma Shows_Server_Agent_not_evs [rule_format]:
  "evs \<in> sdaptrans \<Longrightarrow> Shows (Smartphone Server) A X \<notin> set evs"

  apply (erule sdaptrans.induct)
  apply (simp_all)
  apply (blast dest:Scans_Server_Agent_not_evs)+
done


(* - Server expected message form to the sender *)

lemma Says_Server_DT2 :
  "\<lbrakk> Says Server A \<lbrace> 
       \<lbrace>Agent A, Number T\<rbrace>, 
       Crypt (shrK A) (Nonce r), 
       Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> 
     \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> Gets Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done

(* - The Server only authorizes a transaction if 
     it received a nonce that matches the produced TAN *)

lemma Says_Server_DT8 :
  "\<lbrakk> Server \<noteq> A;
    Says Server A \<lbrace> Agent A, Number T \<rbrace> \<in> set evs;
    evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> \<exists> r.
      Gets Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs \<and>
      Says Server A \<lbrace> 
        \<lbrace>Agent A, Number T\<rbrace>, 
        Crypt (shrK A) (Nonce r),
        Crypt (shrK A) \<lbrace>\<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r)\<rbrace>
      \<rbrace> \<in> set evs \<and>
      Gets Server (Nonce r) \<in> set evs"

  apply (erule rev_mp)
  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (auto)
done




(* 2. General guarantees on smartphones usability *)

(* - Defining legalUse conditions *)

lemma Scans_Smartphone_legalUse :
  "\<lbrakk> Scans A (Smartphone A) X \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> legalUse(Smartphone A)"
apply (erule rev_mp, erule sdaptrans.induct)
apply (auto)
done

lemma Shows_Smartphone_legalUse :
  "\<lbrakk> Shows (Smartphone A) A X \<in> set evs; evs \<in> sdaptrans \<rbrakk> \<Longrightarrow> legalUse(Smartphone A)"
apply (erule rev_mp, erule sdaptrans.induct)
apply (auto)
done


(* - Legal agents' smartphones firing Scans/Shows must be their owners
     performing a legal action or the Spy performing an illegal action *)

lemma Scans_Smartphone :
  "\<lbrakk> Scans A P X \<in> set evs; A \<noteq> Spy; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (P = (Smartphone A) \<and> legalUse(P)) \<or> (P = (Smartphone Spy) \<and> illegalUse(P))"
  
  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done

lemma Shows_Smartphone :
  "\<lbrakk> Shows P A X \<in> set evs; A \<noteq> Spy; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (P = (Smartphone A) \<and> legalUse(P)) \<or> (P = (Smartphone Spy))"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (simp_all)
done

lemma Scans_Shows_Smartphone :
  "\<lbrakk> Scans A P X \<in> set evs \<or> Shows P A X \<in> set evs; A \<noteq> Spy; evs \<in> sdaptrans \<rbrakk>
     \<Longrightarrow> (P = (Smartphone A) \<and> legalUse(Smartphone A))"

  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (simp_all)
  apply (blast)+
done


(* - The spy can act both legally (using her smartphone) or illegally (using someone else) *)
lemma Scans_Smartphone_Spy :
  "\<lbrakk> Scans Spy P X \<in> set evs \<or> Shows P Spy X \<in> set evs; evs \<in> sdaptrans \<rbrakk>  
      \<Longrightarrow> (P = (Smartphone Spy)) \<and> (legalUse(Smartphone Spy)) \<or>  
          (\<exists> A. P = (Smartphone A) \<and> illegalUse(Smartphone A))"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done




(* 3. Protocol termination  *)

lemma Protocol_terminates :
  "\<exists> A T. \<exists> evs \<in> sdaptrans. A \<noteq> Server \<and> Says Server A \<lbrace> Agent A, Number T \<rbrace> \<in> set evs"

  apply (intro exI bexI)
  apply (rule_tac [2] sdaptrans.Nil [THEN sdaptrans.DT1, THEN sdaptrans.Rcpt,
        THEN sdaptrans.DT2, THEN sdaptrans.Rcpt,
        THEN sdaptrans.DT3, THEN sdaptrans.DT4, 
        THEN sdaptrans.DT5, THEN sdaptrans.DT6, 
        THEN sdaptrans.DT7, THEN sdaptrans.Rcpt,
        THEN sdaptrans.DT8])
  apply (possibility, auto)
done




(* 4. Scans & Inputs events guarantees *)

lemma Scans_A_Smartphone_3 :
  "\<lbrakk> Scans A P \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; A \<noteq> Spy; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs \<and>
        Gets A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (simp_all)
done

(* This is an important guarantee: the protocol legally continues if the agent confirms the 
     outputed message, which contains the transaction *)
lemma Inputs_A_Smartphone_5 :
  "\<lbrakk> Inputs A P \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; A \<noteq> Spy; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        (\<exists> r' h\<^sub>s.
          Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs \<and>
          Gets A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs \<and>
          Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs \<and>
          Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs)"

  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (auto)
done

(* First, we state that Smartphones provide correct Shows when fed with expected Scans.
   Such lemmas guarantee that Smartphones cannot produce unexpected Shows, preventing the
   Spy from having unlimited resources *)
lemma Shows_A_Smartphone_4 :
  "\<lbrakk> Shows P A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        (\<exists> r. Scans A (Smartphone A) \<lbrace>
          \<lbrace>Agent A, Number T\<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (simp_all, force+)
done

(* enfraquecer a regra no smartphone *)
lemma Shows_A_Smartphone_6 :
  "\<lbrakk> Shows P A (Nonce r) \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T. Inputs A P \<lbrace> Agent A, Number T \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (simp_all)
  apply (blast+)
  sledgehammer
  apply (auto)
done


(* 5. Shows events guarantees *) 
lemma Shows_honest_A_Smartphone_4 :
  "\<lbrakk> Shows P A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        (\<exists> r. Scans A (Smartphone A) \<lbrace>
          \<lbrace>Agent A, Number T\<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
        \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (simp_all)
  apply (force+)
done

lemma Shows_honest_A_Smartphone_6 :
  "\<lbrakk> Shows P A (Nonce r) \<in> set evs; A \<noteq> Spy; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (legalUse(P)) \<and> P = (Smartphone A) \<and>
        (\<exists> T. Inputs A (Smartphone A) \<lbrace>Agent A, Number T \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (simp_all, force+)
done


(* Weakest versions *)
lemma Shows_which_Smartphone_4 :
  "\<lbrakk> Shows (Smartphone A) A \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (\<exists> r. Scans A (Smartphone A) \<lbrace>
          \<lbrace>Agent A, Number T\<rbrace>,
          Crypt (shrK A) (Nonce r),
          Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r)\<rbrace>
        \<rbrace> \<in> set evs)"

  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (auto)
done

lemma Shows_which_Smartphone_6 :
  "\<lbrakk> Shows (Smartphone A) A (Nonce r) \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T.
          Scans A (Smartphone A) \<lbrace>
            \<lbrace>Agent A, Number T\<rbrace>,
            Crypt (shrK A) (Nonce r),
            Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
          \<rbrace> \<in> set evs \<and>
          Inputs A (Smartphone A) \<lbrace>Agent A, Number T \<rbrace> \<in> set evs)"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done



(* Messages form guarantees *)
lemma Scans_A_Smartphone_form_3 :
  "\<lbrakk> Scans A (Smartphone A) \<lbrace> Transaction, r', h\<^sub>s \<rbrace> \<in> set evs; 
     \<forall> p q. Transaction = \<lbrace>p, q\<rbrace>; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (\<exists> T r. Transaction = \<lbrace> Agent A, Number T \<rbrace>)"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done

lemma Shows_A_Smartphone_form_4 :
  "\<lbrakk> Shows (Smartphone A) A Transaction \<in> set evs; evs \<in> sdaptrans;
    \<forall> p q. Transaction = \<lbrace>p, q\<rbrace> \<rbrakk>
    \<Longrightarrow> \<exists> T. Transaction = \<lbrace>Agent A, Number T\<rbrace>"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done

lemma Shows_A_Smartphone_form_6 :
  "\<lbrakk> Shows (Smartphone A) A TAN \<in> set evs; evs \<in> sdaptrans;
    \<forall> p q. TAN \<noteq> \<lbrace>p, q\<rbrace> \<rbrakk>
    \<Longrightarrow> \<exists> r. TAN = (Nonce r)"

  apply (erule rev_mp, erule sdaptrans.induct)
  apply (auto)
done



(* 6. SPY COUNTERGUARANTEES *)
lemma Spy_knows_Transaction : 
  "\<lbrakk> Says A Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
     \<Longrightarrow> Number T \<in> analz (knows Spy evs)"
by (blast dest!: Says_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd])

lemma Spy_knows_TAN :
  "\<lbrakk> Says A Server (Nonce r) \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> Nonce r \<in> knows Spy evs"
by (blast dest!: Says_imp_knows_Spy)


lemma TAN_Says_Server_analz_knows_Spy :
  "\<lbrakk> Says Server A \<lbrace>
       \<lbrace>Agent A, Number T\<rbrace>,
       Crypt (shrK A) (Nonce r),
       Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
     \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
  \<Longrightarrow> Crypt (shrK A) (Nonce r) \<in> analz (knows Spy evs)"

  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (simp_all add: analz_insertI)
done

lemma Hash_Says_Server_analz_knows_Spy :
  "\<lbrakk> Says Server A \<lbrace>
       \<lbrace>Agent A, Number T\<rbrace>,
       Crypt (shrK A) (Nonce r),
       Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
     \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
  \<Longrightarrow> Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> \<in> analz (knows Spy evs)"

  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (simp_all add: analz_insertI)
done

lemma TAN_Scans_analz_knows_Spy :
  "\<lbrakk> Scans A (Smartphone A) \<lbrace>
       \<lbrace>Agent A, Number T\<rbrace>,
       Crypt (shrK A) (Nonce r),
       Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> 
     \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
  \<Longrightarrow> Crypt (shrK A) (Nonce r) \<in> analz (knows Spy evs)"

  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (simp_all add: analz_insertI)
  apply (blast dest!: DT3_analz_knows_Spy_fst)+
done

lemma Hash_Scans_analz_knows_Spy :
  "\<lbrakk> Scans A (Smartphone A) \<lbrace>
       \<lbrace>Agent A, Number T\<rbrace>,
       Crypt (shrK A) (Nonce r),
       Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> 
     \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
  \<Longrightarrow> Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> \<in> analz (knows Spy evs)"

  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (simp_all add: analz_insertI)
  apply (blast dest!: DT3_analz_knows_Spy_snd)+
done



(* REGULARITY LEMMAS *)
lemma Spy_parts_keys [simp] : 
  "evs \<in> sdaptrans \<Longrightarrow> (Key (shrK A) \<in> parts (knows Spy evs)) = (Smartphone A \<in> badP)"

  apply (erule sdaptrans.induct)
  apply (frule_tac [4] DT3_parts_knows_Spy_fst)
  apply (frule_tac [5] DT3_parts_knows_Spy_snd)
  apply (simp_all)
  apply (auto intro!:parts_insertI)
done

lemma Spy_analz_shrK [simp] :
  "evs \<in> sdaptrans \<Longrightarrow> (Key (shrK A) \<in> analz (knows Spy evs)) = (Smartphone A \<in> badP)" 
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
    evs \<in> sdaptrans\<rbrakk>
   \<Longrightarrow> A = A' \<and> T = T'"

  apply (erule rev_mp)
  apply (erule rev_mp)
  apply (erule sdaptrans.induct)  
  apply (simp_all)
  apply (fastforce dest: Says_parts_used)
done

lemma aux : 
  "\<lbrakk> Gets A \<lbrace>\<lbrace>Agent A, Number T\<rbrace>, r', hs\<rbrace> \<in> set evs;
     Gets A' \<lbrace>\<lbrace>Agent A, Number T\<rbrace>, r', hs\<rbrace> \<in> set evs; A \<noteq> Spy; A' \<noteq> Spy;
      evs \<in> sdaptrans
  \<rbrakk> \<Longrightarrow> A' = A"

  apply (erule rev_mp)
  apply (erule rev_mp)
  apply (erule sdaptrans.induct)  
  apply (simp_all)
  apply auto
sledgehammer
done


lemma Smartphone_transaction_unique2 : 
  "\<lbrakk> Scans A (Smartphone A) \<lbrace>\<lbrace>Agent A, Number T\<rbrace>, r', hs\<rbrace> \<in> set evs;
     Scans A' (Smartphone A') \<lbrace>\<lbrace>Agent A', Number T'\<rbrace>, r', hs\<rbrace> \<in> set evs;
    evs \<in> sdaptrans
  \<rbrakk>
  \<Longrightarrow> A = A' \<and> T = T'"

  apply (erule rev_mp)
  apply (erule rev_mp)
  apply (erule sdaptrans.induct)  
  apply (simp_all)
  apply auto
oops

lemma Smartphone_transaction_unique : 
  "\<lbrakk> Scans A (Smartphone A) \<lbrace>
      \<lbrace>Agent A, Number T\<rbrace>,
      Crypt (shrK A) (Nonce r),
      Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
     \<rbrace> \<in> set evs;
     Scans A' (Smartphone A') \<lbrace>
      \<lbrace>Agent A', Number T'\<rbrace>,
      Crypt (shrK A') (Nonce r),
      Crypt (shrK A') \<lbrace> \<lbrace>Agent A', Number T'\<rbrace>, Crypt (shrK A') (Nonce r) \<rbrace>
     \<rbrace> \<in> set evs;
    evs \<in> sdaptrans
  \<rbrakk>
  \<Longrightarrow> A = A' \<and> T = T'"

  apply (erule rev_mp)
  apply (erule rev_mp)
  apply (erule sdaptrans.induct)  
  apply (simp_all)
  defer
  apply (blast)
oops

(* We do not force that a transaction number T to be fresh, hence we cannot prove the
   following  
lemma Server_TAN_unique :
  "\<lbrakk> Says Server A \<lbrace> 
      \<lbrace>Agent A, Number T\<rbrace>,
      Crypt (shrK A) (Nonce r),
      Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>
    \<rbrace> \<in> set evs ;
    Says Server A \<lbrace> 
      \<lbrace>Agent A, Number T\<rbrace>,
      Crypt (shrK A) (Nonce r'),
      Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r') \<rbrace>
     \<rbrace> \<in> set evs;
    evs \<in> sdaptrans\<rbrakk>
   \<Longrightarrow> r = r'"
*)

(* AUTHENTICITY LEMMAS *)
lemma Ciphers_authentic :
  "\<lbrakk> Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> parts (knows Spy evs);
     (Smartphone A) \<notin> badP; evs \<in> sdaptrans \<rbrakk>
     \<Longrightarrow> r' = Crypt (shrK A) (Nonce r) \<and>
         h\<^sub>s = Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r)\<rbrace> \<and>
         Says Server A \<lbrace>
            \<lbrace>Agent A, Number T\<rbrace>,
            Crypt (shrK A) (Nonce r),
            Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace> 
         \<rbrace> \<in> set evs"
      
  apply (erule rev_mp, erule sdaptrans.induct)
  apply (simp_all (no_asm_simp))
  apply (auto)
done

(* CONFIDENTIALITY LEMMAS *)


(* AUTHENTICATION LEMMAS *)


(* AUTHORIZATION LEMMAS *)

(* INTEGRITY LEMMAS *)
text\<open>@{term step2_integrity} also is a reliability theorem\<close>
lemma Says_Server_message_form_DT2 :
  "\<lbrakk> Says Server A \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
    \<Longrightarrow> (\<exists> r.
         r' = Crypt (shrK A) (Nonce r) \<and>
         h\<^sub>s = Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>)"

  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (auto)
done

text\<open>@{term step3_integrity} is the form of the message which the agent redirect to its smartphone.
It cannot be proven, since there is no way to the agent know what he is forwarding \<close>
(* lemma Scans_Smartphone_A_DT3_message_form :
  "\<lbrakk> A \<noteq> Spy; Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
  \<Longrightarrow> (\<exists> r.
        r' = Crypt (shrK A) (Nonce r) \<and>
        h\<^sub>s = Crypt (shrK A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, Crypt (shrK A) (Nonce r) \<rbrace>)"
*)

lemma Scans_Smartphone_A_DT3_message_form_unprovable : 
  "\<lbrakk> Scans A (Smartphone A) \<lbrace> \<lbrace>Agent A, Number T\<rbrace>, r', h\<^sub>s \<rbrace> \<in> set evs; evs \<in> sdaptrans \<rbrakk>
  \<Longrightarrow> (\<exists> r'. (\<exists> r. r' \<noteq> Crypt (shrK A) (Nonce r)))"
  apply (erule rev_mp)
  apply (erule sdaptrans.induct)
  apply (auto)
done

end