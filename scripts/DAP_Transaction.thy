(*
  Title: Dynamic Authorization Protocol - Message Transaction
  Author: Felipe Rodopoulos de Oliveira
*)

theory DAP_Transaction imports "./Smartphone"

begin

inductive_set daptrans :: "event list set" where
  Nil: "[] \<in> daptrans"

  | DT1: "\<lbrakk> evs1 \<in> daptrans \<rbrakk>
    \<Longrightarrow> Says A Server \<lbrace>Agent A, Number T\<rbrace> # evs1 \<in> daptrans"

  | DT2: "\<lbrakk> evs2 \<in> daptrans;
          Says A' Server \<lbrace>Agent A, Number T\<rbrace> \<in> set evs2;
          Nonce r \<notin> used evs2;
          r' = Crypt (shrK K) (Nonce r);
          h_s = Hash \<lbrace> \<lbrace>Agent A, Number T \<rbrace>, r' \<rbrace> \<rbrakk>
    \<Longrightarrow> Says Server A \<lbrace> Transaction, r', h_s \<rbrace> # evs2 \<in> daptrans"

  | DT3: "\<lbrakk> evs3 \<in> daptrans;
            Says A Server Transaction \<in> set evs3;
            Gets A \<lbrace> Transaction, r', h_s \<rbrace> \<in> set evs3 \<rbrakk> 
    \<Longrightarrow> Inputs A (Smartphone A) \<lbrace> Transaction, r', h_s \<rbrace> # evs3 \<in> daptrans"

  | DT4: "\<lbrakk> evs4 \<in> daptrans; 
            Gets_s (Smartphone A) \<lbrace> Transaction, r', h_s \<rbrace>;  
            h_u = Hash (Transaction, r'); h_s == h_u \<rbrakk> 
    \<Longrightarrow> Outputs (Smartphone A) A Transaction # evs4 \<in> daptrans"

  | DT5: "\<lbrakk> evs5 \<in> daptrans;
            Inputs A (Smartphone A) \<lbrace> Transaction, r', h_s \<rbrace>;
            Gets_a A Transaction'; Transaction == Transaction' \<rbrakk> 
    \<Longrightarrow> Inputs A (Smartphone A) Confirmation # evs4 \<in> daptrans"

  | DT6: "\<lbrakk> evs6 \<in> daptrans; 
            Gets_s (Smartphone A) \<lbrace> Transaction, r', h_s \<rbrace>;
            Outputs (Smartphone A) A Transaction; 
            Gets_s (Smartphone A) Confirmation; Confirmation == True;
            r_u \<notin> used evs6 \<rbrakk> 
   \<Longrightarrow> Outputs (Smartphone A) A r_u # evs6 \<in> daptrans"

   (* TODO *)
   | DT7: "\<lbrakk> evs7 \<in> daptrans \<rbrakk> \<Longrightarrow> Says A Server r_u # evs7 \<in> daptrans"

  | Fake: "\<lbrakk>evsf \<in> daptrans; X \<in> synth(analz(spies evsf))\<rbrakk> \<Longrightarrow> Says Spy B X # evsf \<in> daptrans"


lemma Protocol_terminates :
  "\<exists>r. \<exists>evs \<in> daptrans. Says A Server (Nonce r) \<in> set evs"
apply (intro exI bexI)
sorry

end