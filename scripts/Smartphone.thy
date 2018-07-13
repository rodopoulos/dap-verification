(*  Title:      Smartphone.thy
    Author:     Felipe Rodopoulos, University of Brasilia
    Copyright   2018  University of Brasilia

Theory for offline and out-of-band channels, defined by the communications
  means created using the smartphone camera for decoding QR codes displayed
  at other insecure devices screens.

Definitions for keys, initial state of agents and smartphone's usability.

An agent is bad if her smartphone is connected in the unreliable channel and
it is compromised.

*)

theory Smartphone imports "./EventSP" "~~/src/HOL/Auth/All_Symmetric" begin

axiomatization
  shrK  ::  "agent \<Rightarrow> key"

where
  inj_shrK : "inj shrK"

definition legalUse :: "smartphone \<Rightarrow> bool" ("legalUse (_)") where
  "legalUse P == P \<notin> stolen"
  
definition illegalUse :: "smartphone \<Rightarrow> bool" ("illegalUse (_)") where
  "illegalUse P == P \<in> stolen"

  
(* === EXTENDING AGENTS' INITIAL STATE === *)
overloading initState \<equiv> initState
  begin
  primrec initState where
    initState_Server : "initState Server = (Key`(range shrK))" |
    initState_Friend : "initState (Friend i) = {Key (shrK(Friend i))}" |
    initState_Spy : "initState Spy = (Key`((shrK` bad) \<union> (shrK`{A. Smartphone A \<in> (badp \<inter> connected)}) ))"
end

axiomatization where
  Key_sypply_ax: "finite KK \<Longrightarrow> \<exists> K. K \<notin> KK & Key K \<notin> used evs "


(* PROPERTIES OF SHARED KEYS *)
declare inj_shrK [THEN inj_eq, iff]

lemma invKey_K [simp]: "invKey K = K"
apply (insert isSym_keys)
apply (simp add: symKeys_def)
done

(* This is trivial given two facts:
  1. invKey K = K, so K decrypts anything encryted with K
  2. Given that, this lemma follow the structure of the last fact that defines the analz operator
*)
lemma analz_Decrypt' [dest]:
  "\<lbrakk> Crypt K X \<in> analz H; Key K \<in> analz H \<rbrakk> \<Longrightarrow> X \<in> analz H"
apply (auto)
done
declare analz.Decrypt [rule del]


lemma parts_image_Nonce [simp]: "parts (Nonce` N) = Nonce` N"
apply (auto)
done

(* Since we are talking about shared keys only, no keys can be obtained from initial states *)
lemma keysFor_parts_initState [simp] : 
  "keysFor (parts (initState C)) = {}"
apply (unfold keysFor_def)
apply (induct_tac "C", auto)
done

(* Specific for shared keys: a key used for encrypt a message must coexist in the same message
set of that message or came from some other message set *)
lemma keysFor_parts_insert : 
  "\<lbrakk> K \<in> keysFor (parts (insert X G)); X \<in> synth (analz H) \<rbrakk>
    \<Longrightarrow> K \<in> keysFor (parts (G \<union> H)) | Key K \<in> parts H"
by (force dest: EventSP.keysFor_parts_insert)

(* The key for an encryption must coexist in the same set where the encryption was created *)
lemma Crypt_imp_keysFor : 
  "Crypt K X \<in> H \<Longrightarrow> K \<in> keysFor H"
by (drule Crypt_imp_invKey_keysFor, simp)


(* Server does know all shared keys! *)
lemma shrK_in_initState [iff]: "Key (shrK A) \<in> initState Server"
apply (induct_tac "A")
apply auto
done

lemma shrK_in_used [iff]: "Key (shrK A) \<in> used evs"
apply (rule initState_into_used)
apply blast
done

(* Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
   from long-term shared keys *)
lemma Key_not_used [simp]: "Key K \<notin> used evs \<Longrightarrow> K \<notin> range shrK"
by blast

lemma shrK_neq [simp]: "Key K \<notin> used evs \<Longrightarrow> shrK B \<noteq> K"
by blast

declare shrK_neq [THEN not_sym, simp]

end