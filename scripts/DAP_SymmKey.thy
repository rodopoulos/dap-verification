(*
  Title: Dynamic Authorization Protocol - Message Transaction
  Author: Felipe Rodopoulos de Oliveira
*)

theory DAP_SymmKey imports "./Smartphone"

begin

inductive_set dapskey :: "event list set" where
  Nil: "[] \<in> dapskey"

  | DK1: "\<lbrakk> evs1 \<in> dapskey; A \<noteq> Server \<rbrakk>
    \<Longrightarrow> Says A Server (Agent A) # evs1 \<in> dapskey"

  | DK2: "\<lbrakk> evs2 \<in> dapskey;
            Gets Server (Agent A) \<in> set evs2;
            Nonce N\<^sub>K \<notin> used evs2 \<rbrakk>
    \<Longrightarrow> Says Server A (Nonce N\<^sub>K) # evs2 \<in> dapskey"

  | DK3: "\<lbrakk> evs3 \<in> dapskey; legalUse (Smartphone A);
            Says A Server (Agent A) \<in> set evs3;
            Gets A (Nonce N\<^sub>K) \<in> set evs3 \<rbrakk>
    \<Longrightarrow> Inputs A (Smartphone A) (Nonce N\<^sub>K) # evs3 \<in> dapskey"

  | DK4: "\<lbrakk> evs4 \<in> dapskey;
            Says A Server (Agent A) \<in> set evs4;
            Gets A (Nonce N\<^sub>K) \<in> set evs4;
            Inputs A (Smartphone A) (Nonce N\<^sub>K) \<in> set evs4 \<rbrakk>
    \<Longrightarrow> Says A ATM (Agent A) # evs4 \<in> dapskey"

  | DT5: "\<lbrakk> evs5 \<in> dapskey; legalUse(Smartphone A);
            Gets ATM (Agent A) \<in> set evs5;
            (Nonce K') \<notin> used evs5 \<rbrakk>
    \<Longrightarrow> Inputs ATM (Smartphone A) (Nonce K') # evs5 \<in> dapskey"

  | DT6: "\<lbrakk> evs6 \<in> dapskey; legalUse(Smartphone A);
            Gets_s (Smartphone A) (Nonce N\<^sub>K) \<in> set evs6;
            Gets_s (Smartphone A) (Nonce K') \<in> set evs6 \<rbrakk>
   \<Longrightarrow> Notes_s (Smartphone A) (Key K) # evs6 \<in> dapskey"

  (* Rule modeling the illegal behavior of the Spy *)
  | Fake: "\<lbrakk> evsF \<in> dapskey; X \<in> synth(analz(knows Spy evsF));
             illegalUse(Smartphone A); C \<noteq> Server; C \<noteq> Spy \<rbrakk>
    \<Longrightarrow> Says Spy B X #
        Inputs Spy (Smartphone A) X #
        Outputs (Smartphone Spy) C X # evsF \<in> dapskey"
  
  (* Reception invariant rules *)
  | Rcpt: "\<lbrakk> evsR \<in> dapskey; Says A B X \<in> set evsR \<rbrakk> \<Longrightarrow> Gets B X # evsR \<in> dapskey"

  | Rcpt_s: "\<lbrakk> evsRs \<in> dapskey; Inputs A (Smartphone B) X \<in> set evsRs \<rbrakk> 
    \<Longrightarrow> Gets_s (Smartphone B) X # evsRs \<in> dapskey"

  | Rcpt_a: "\<lbrakk> evsRa \<in> dapskey; Outputs (Smartphone A) B X \<in> set evsRa \<rbrakk>
    \<Longrightarrow> Gets_a B X # evsRa \<in> dapskey"
