(*
  Title: Dynamic Authorization Protocol - Message Transaction
  Author: Felipe Rodopoulos de Oliveira
*)

theory DAP_Transaction imports "~~/src/HOL/Auth/Public"

begin

inductive_set daptrans :: "event list set" where
  Nil: "[] \<in> daptrans"

  | DT1: "\<lbrakk> evs1 \<in> daptrans \<rbrakk>
    \<Longrightarrow> Says A Server (Number T) # evs1 \<in> daptrans"

  | DT2: "\<lbrakk> evs2 \<in> daptrans;
          Says A Server Transaction \<in> set evs2;
          Nonce r \<notin> used evs2;
          r' = Crypt k2 (Nonce r);
          k2 \<in> symKeys;
          h_s = Hash \<lbrace> Transaction, r' \<rbrace>
        \<rbrakk>
    \<Longrightarrow> Says Server A \<lbrace> Transaction, r', h_s \<rbrace> # evs2 \<in> daptrans"

  | DT3: "\<lbrakk> evs3 \<in> daptrans;
          Says A Server Transaction \<in> set evs3;
          Says S A \<lbrace> Transaction', r', h_s \<rbrace> \<in> set evs3;
          h_u = Hash \<lbrace> Transaction', r' \<rbrace>;
          h_s = h_u 
        \<rbrakk> 
    \<Longrightarrow> Says A Server (Nonce r) # evs3 \<in> daptrans"

  | Fake: "\<lbrakk>evsf \<in> daptrans; X \<in> synth(analz(spies evsf))\<rbrakk> \<Longrightarrow> Says Spy B X # evsf \<in> daptrans"


lemma Protocol_terminates :
  "\<exists>r. \<exists>evs \<in> daptrans. Says A Server (Nonce r) \<in> set evs"
  apply (intro exI bexI)
  apply (rule_tac [2] daptrans.DT3)
  apply (rule_tac [2] daptrans.DT2)
  apply (rule_tac [2] daptrans.DT1)
  apply (rule_tac [2] daptrans.Nil)
  apply (possibility)
  done

end