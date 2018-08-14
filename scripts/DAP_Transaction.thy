(*
  Title: Dynamic Authorization Protocol - Message Transaction
  Author: Felipe Rodopoulos de Oliveira
*)

theory DAP_Transaction imports "./Smartphone"

begin

abbreviation
  Confirmation :: msg where "Confirmation \<equiv> (Number 1)"
abbreviation
  Success :: msg where "Success \<equiv> (Number 1)"

inductive_set daptrans :: "event list set" where
  Nil: "[] \<in> daptrans"


  | DT1: "\<lbrakk> evs1 \<in> daptrans \<rbrakk>
    \<Longrightarrow> Says A Server \<lbrace> Agent A, Number T \<rbrace> # evs1 \<in> daptrans"

  | DT2: "\<lbrakk> evs2 \<in> daptrans;
          Gets Server \<lbrace> Agent A, Number T \<rbrace> \<in> set evs2;
          Nonce r \<notin> used evs2;
          r' = Crypt (shrK A) (Nonce r);
          h_s = Hash \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r' \<rbrace> \<rbrakk>
    \<Longrightarrow> Says Server A \<lbrace> \<lbrace> Agent A, Number T \<rbrace>, r', h_s \<rbrace> # evs2 \<in> daptrans"

  | DT3: "\<lbrakk> evs3 \<in> daptrans;
            Says A Server Transaction \<in> set evs3;
            Gets A \<lbrace> Transaction, r', h_s \<rbrace> \<in> set evs3 \<rbrakk> 
    \<Longrightarrow> Inputs A (Smartphone A) \<lbrace> Transaction, r', h_s \<rbrace> # evs3 \<in> daptrans"

  | DT4: "\<lbrakk> evs4 \<in> daptrans;
            Gets_s (Smartphone A) \<lbrace> Transaction', r', h_s \<rbrace> \<in> set evs4;
            h_u = Hash \<lbrace> Transaction', r' \<rbrace>;
            h_s == h_u \<rbrakk> 
    \<Longrightarrow> Outputs (Smartphone A) A Transaction' # evs4 \<in> daptrans"

  | DT5: "\<lbrakk> evs5 \<in> daptrans;
            Says A Server Transaction \<in> set evs5;
            Gets S \<lbrace> Transaction, r', h_u \<rbrace> \<in> set evs5;
            Inputs A (Smartphone A) \<lbrace> Transaction, r', h_s \<rbrace> \<in> set evs5;
            Gets_a A Transaction' \<in> set evs5;
            Transaction == Transaction' \<rbrakk>
    \<Longrightarrow> Inputs A (Smartphone A) Confirmation # evs5 \<in> daptrans"

  | DT6: "\<lbrakk> evs6 \<in> daptrans; 
            Gets_s (Smartphone A) \<lbrace> Transaction', r', h_s \<rbrace> \<in> set evs6;
            Outputs (Smartphone A) A Transaction' \<in> set evs6; 
            Gets_s (Smartphone A) Confirmation \<in> set evs6;
            r_u \<notin> used evs6 \<rbrakk> 
   \<Longrightarrow> Outputs (Smartphone A) A r_u # evs6 \<in> daptrans"

  | DT7: "\<lbrakk> evs7 \<in> daptrans;
            Says A Server Transaction \<in> set evs7;
            Gets S \<lbrace> Transaction, r', h_u \<rbrace> \<in> set evs7; 
            Inputs A (Smartphone A) \<lbrace> Transaction, r', h_u\<rbrace> \<in> set evs7;
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

  | Fake: "\<lbrakk> evsf \<in> daptrans; X \<in> synth(analz(knows Spy evsf)) \<rbrakk> \<Longrightarrow> Says Spy B X # evsf \<in> daptrans"
    
  | Rcpt: "\<lbrakk> evsr \<in> daptrans; Says A B X \<in> set evsr \<rbrakk> \<Longrightarrow> Gets B X # evsr \<in> daptrans"

  | Rcpt_s: "\<lbrakk> evsRs \<in> daptrans; Inputs A (Smartphone B) X \<in> set evsRs \<rbrakk> 
    \<Longrightarrow> Gets_s (Smartphone B) X # evsRc \<in> daptrans"

  | Rcpt_a: "\<lbrakk> evsRa \<in> daptrans; Outputs (Smartphone A) B X \<in> set evsRa \<rbrakk>
    \<Longrightarrow> Gets_a B X # evsRa \<in> daptrans"


lemma DT3_happens:
  "\<exists> T r h. \<exists>evs \<in> daptrans. Inputs A (Smartphone A) \<lbrace> T, r, h \<rbrace> \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.Nil 
        [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3])
apply (possibility, auto)
done

lemma DT4_happens:
  "\<exists> T. \<exists>evs \<in> daptrans. Outputs (Smartphone A) A T \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] daptrans.Nil 
        [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3, THEN daptrans.Rcpt_s,
        THEN daptrans.DT4])
apply (possibility, auto)
done

lemma DT5_happens:
  "\<exists> C. \<exists>evs \<in> daptrans. Inputs A (Smartphone A) C \<in> set evs"
apply (intro exI bexI)
(*apply (rule_tac [2] daptrans.Nil
        [THEN daptrans.DT1, THEN daptrans.Rcpt,
        THEN daptrans.DT2, THEN daptrans.Rcpt,
        THEN daptrans.DT3, THEN daptrans.Rcpt_s,
        THEN daptrans.DT4, THEN daptrans.Rcpt_a,
        THEN daptrans.DT5])*)
apply (rule_tac [2] daptrans.DT5)
apply (rule_tac [2] daptrans.Rcpt_a)
apply (rule_tac [2] daptrans.DT4)
apply (rule_tac [2] daptrans.Rcpt_s)
apply (rule_tac [2] daptrans.DT3)
apply (rule_tac [2] daptrans.Rcpt)
apply (rule_tac [2] daptrans.DT2)
apply (rule_tac [2] daptrans.Rcpt)
apply (rule_tac [2] daptrans.DT1)
apply (rule_tac [2] daptrans.Nil)
apply (possibility)
apply (auto)
done

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