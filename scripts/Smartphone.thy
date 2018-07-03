(*  Title:      Smartphone.thy
    Author:     Felipe Rodopoulos, University of Brasilia
    Copyright   2018  University of Brasilia

Theory for offline and out-of-band channels, defined by communications
  means created using the smartphone camera for decoding QR codes displayed
  at other insecure devices screens.

Definitions for keys, initial state of agents and smartphone's usability.
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

lemma analz_Decrypt' [dest]:
  "\<lbrakk> Crypt K X \<in> analz H; Key K \<in> analz H \<rbrakk> \<Longrightarrow> X \<in> analz H"
apply (auto)
done
declare analz.Decrypt [rule del]

lemma parts_image_Nonce [simp]: "parts (Nonce`N) = Nonce`N"
apply (auto)
done

lemma keysFor_parts_initState [simp] : 
  "keysFor (parts (initState C)) = {}"
apply (unfold keysFor_def)
apply (induct_tac "C", auto)
done

(* IF a key K is present in the set of useful keys to decrypt message X in a given message set G
 and  message X can be constructed given analysis of a message set H,
 THEN key K must be either in set G or H  *)
lemma keysFor_parts_insert : 
  "\<lbrakk> K \<in> keysFor (parts (insert X G)); X \<in> synth (analz H) \<rbrakk>
    \<Longrightarrow> K \<in> keysFor (parts (G \<union> H)) | Key K \<in> parts H"
by (force dest: EventSP.keysFor_parts_insert)


lemma Crypt_imp_keysFor : 
  "Crypt K X \<in> H \<Longrightarrow> K \<in> keysFor H"
by (drule Crypt_imp_invKey_keysFor, simp)


end