(*  Title:      Smartphone.thy
    Author:     Felipe Rodopoulos, University of Brasilia
    Copyright   2018 University of Brasilia

Theory for offline and out-of-band channels, defined by the communications
  means created by the usage of a smartphone camera for decoding QR codes 
  displayed others devices screens.

Definitions for keys, initial state of agents and smartphone's usability.

An agent is bad if her smartphone is both connected to the unreliable channel 
  and compromised.

*)

theory Smartphone imports "./EventSP" "~~/src/HOL/Auth/All_Symmetric" begin

(* Theory only reasons over pre-shared keys between agents and Servers.
  Any other key type must be defined in another theory *)
axiomatization
  shrK  ::  "agent \<Rightarrow> key"

where
  inj_shrK : "inj shrK"


  
(* SMARTPHONE USAGE *)
(* Legal agents use their smartphone if they hold it *)
definition legalUse :: "smartphone \<Rightarrow> bool" ("legalUse (_)") where
  "legalUse P == P \<notin> stolen"

(* Smartphones are prone to theft. The Spy may use it if she have stole it. *)
definition illegalUse :: "smartphone \<Rightarrow> bool" ("illegalUse (_)") where
  "illegalUse P == P \<in> stolen"


  
(* AGENTS' INITIAL STATE *)
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

(* Shared key encryption is symmetric *)
lemma invKey_K [simp]: "invKey K = K"
apply (insert isSym_keys)
apply (simp add: symKeys_def)
done

(* An agent who has a cipher and its correspondet key, can retrieve the message from the cipher's
   body. Trivial, given two facts:
    1. invKey K = K, so K decrypts anything encryted with K
    2. Given that, this lemma follow the structure of the last fact that defines the analz operator
*)
lemma analz_Decrypt' [dest]:
  "\<lbrakk> Crypt K X \<in> analz H; Key K \<in> analz H \<rbrakk> \<Longrightarrow> X \<in> analz H"
apply (erule analz.Decrypt)
apply (simp)
done

(* Removing the <dest> atribute of <analz.Decrypt> in the analz declaration *)
declare analz.Decrypt [rule del]

(* parts predicate idempotency on nonces *)
lemma parts_image_Nonce [simp]: "parts (Nonce` N) = Nonce` N"
apply (auto)
done

(* *)
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

(* Following lemmas are used in parts_induct_tac and analz_Fake_tac to distinguish session keys
   from long-term shared keys *)

(* If a key is fresh, then it must not  *)
lemma Key_not_used [simp]: "Key K \<notin> used evs \<Longrightarrow> K \<notin> range shrK"
by blast

lemma shrK_neq [simp]: "Key K \<notin> used evs \<Longrightarrow> shrK B \<noteq> K"
by blast

declare shrK_neq [THEN not_sym, simp]



(* NONCE LEMMAS *)
(* Nonces must be fresh! So no nonces in initial state of agents knowledge *)
lemma Nonce_notin_initState [iff]: "Nonce N \<notin> parts (initState (Friend i))"
by auto

lemma subset_Compl_range_shrK: "A \<subseteq> - (range shrK) \<Longrightarrow> shrK x \<notin> A"
by blast

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} \<union> H"
by blast

lemma insert_Key_image: "insert (Key K) (Key`KK \<union> C) = Key`(insert K KK) \<union> C"
by blast



end