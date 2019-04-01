(*  Title:      Smartphone.thy
    Author:     Felipe Rodopoulos, University of Brasilia
    Copyright   2018 University of Brasilia

Theory for offline and out-of-band channels. These are defined by the
communications means created by the usage of a smartphone camera for
decoding QR codes displayed others devices screens.

Definitions for keys, initial state of agents and smartphone's usability.

An agent is bad if her smartphone is compromised.

*)

theory Smartphone imports "./EventSP" "~~/src/HOL/Auth/All_Symmetric" begin

(* Theory only reasons over pre-shared keys between agents smartphones and Servers *)
axiomatization
  shrK  ::  "agent \<Rightarrow> key"

where
  inj_shrK : "inj shrK"


  
(* SMARTPHONE USAGE *)
(* Legal agents use their smartphone if they hold it *)
definition legalUse :: "smartphone \<Rightarrow> bool" ("legalUse (_)") where
  "legalUse P == P \<notin> stolen"

(* Smartphones are prone to theft. The Spy may use it if she have stole it.
   If devices can be compromised, the Spy can remotely obtain its inputs and outputs *)
primrec illegalUse :: "smartphone \<Rightarrow> bool" where
  illegalUse_def: "illegalUse (Smartphone A) = (
    (insecureP \<and> (Smartphone A \<in> stolen) \<or> (Smartphone A \<in> badP)) \<or>
    (secureP   \<and> (Smartphone A \<in> stolen)))"


  
(* AGENTS' INITIAL STATE *)
overloading initState \<equiv> initState
  begin
  primrec initState where
    initState_Server : "initState Server = (Key` (range shrK))" |
    initState_Friend : "initState (Friend i) = {}" |
    initState_Spy : "initState Spy = (Key` (shrK` {A. Smartphone A \<in> badP}))"
end

axiomatization where
  Key_supply_ax: "finite KK \<Longrightarrow> \<exists> K. K \<notin> KK & Key K \<notin> used evs " and
  
  (*Needed because of Spy's knowledge of Pairkeys*)
  Nonce_supply_ax: "finite NN \<Longrightarrow> \<exists> N. N \<notin> NN & Nonce N \<notin> used evs"


  
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
lemma parts_image_Nonce [simp] :
  "parts (Nonce` N) = Nonce` N"
by auto

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
apply simp_all
done

(* Previous to any session, legal agents only know their keys *)
lemma shrK_not_in_other [iff]: "Key (shrK (Friend x)) \<in> initState (Friend y) \<Longrightarrow> (x = y)"
apply simp
done

(* Long term keys are not fresh *)
lemma shrK_in_used [iff]: "Key (shrK A) \<in> used evs"
apply (rule initState_into_used)
apply blast
done


(* Following lemmas are used in parts_induct_tac and analz_Fake_tac to distinguish session keys
   from long-term shared keys *)

(* If a key is fresh, then it must not a long-term key *)
lemma Key_not_used [simp]: "Key K \<notin> used evs \<Longrightarrow> K \<notin> range shrK"
by blast

lemma shrK_neq [simp]: "Key K \<notin> used evs \<Longrightarrow> shrK B \<noteq> K"
by blast

declare shrK_neq [THEN not_sym, simp]



(* FUNCTION KNOWS *)
(* An agent's compromised Smartphone disclose hers shared keys *)
lemma Spy_knows_bad_phones [intro!] :
  "Smartphone A \<in> badP \<Longrightarrow> Key (shrK A) \<in> knows Spy evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) add: imageI knows_Cons split: event.split)
done

(* As a consequence, if the Smartphone is robbed, it also disclose the agents secrets to the Spy *)
lemma Spy_knows_stolen_phones [intro!] :
  "Smartphone A \<in> stolen \<Longrightarrow> Key (shrK A) \<in> knows Spy evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) add: imageI knows_Cons split: event.split)
using Stolen_in_badP by blast

(* Case analysis on whether or not an agent is compromised *)
lemma Crypt_Spy_analz_bad :
  "\<lbrakk> Crypt (shrK A) X \<in> analz (knows Spy evs); Smartphone A \<in> badP \<rbrakk> 
    \<Longrightarrow> X \<in> analz (knows Spy evs)"
apply (erule analz.Decrypt)
apply (simp add: Spy_knows_bad_phones)
done



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


lemma Nonce_supply :
  "Nonce (SOME N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule finite.emptyI [THEN Nonce_supply_ax, THEN exE])
apply (rule someI, blast)
done


lemmas analz_image_freshK_simps =
       simp_thms mem_simps \<comment>\<open>these two allow its use with \<open>only:\<close>\<close>
       disj_comms 
       image_insert [THEN sym] image_Un [THEN sym] empty_subsetI insert_subset
       analz_insert_eq Un_upper2 [THEN analz_mono, THEN [2] rev_subsetD]
       insert_Key_singleton subset_Compl_range_shrK
       Key_not_used insert_Key_image Un_assoc [THEN sym]

(*Lemma for the trivial direction of the if-and-only-if*)
lemma analz_image_freshK_lemma:
     "(Key K \<in> analz (Key`nE \<union> H)) \<longrightarrow> (K \<in> nE | Key K \<in> analz H)  \<Longrightarrow>  
         (Key K \<in> analz (Key`nE \<union> H)) = (K \<in> nE | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])


subsection\<open>Tactics for possibility theorems\<close>

ML
\<open>
structure Smartphone =
struct

(*Omitting used_Says makes the tactic much faster: it leaves expressions
    such as  Nonce ?N \<notin> used evs that match Nonce_supply*)
fun possibility_tac ctxt =
   (REPEAT 
    (ALLGOALS (simp_tac (ctxt
      delsimps @{thms used_Cons_simps}
      setSolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac ctxt [refl, conjI, @{thm Nonce_supply}])))

(*For harder protocols (such as Recur) where we have to set up some
  nonces and keys initially*)
fun basic_possibility_tac ctxt =
    REPEAT 
    (ALLGOALS (asm_simp_tac (ctxt setSolver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac ctxt [refl, conjI]))

val analz_image_freshK_ss = 
  simpset_of
   (@{context} delsimps [image_insert, image_Un]
               delsimps [@{thm imp_disjL}]    (*reduces blow-up*)
               addsimps @{thms analz_image_freshK_simps})
end
\<close>


(*Lets blast_tac perform this step without needing the simplifier*)
lemma invKey_shrK_iff [iff]:
     "(Key (invKey K) \<in> X) = (Key K \<in> X)"
by auto

(*Specialized methods*)

method_setup analz_freshK = \<open>
    Scan.succeed (fn ctxt =>
     (SIMPLE_METHOD
      (EVERY [REPEAT_FIRST (resolve_tac ctxt [allI, ballI, impI]),
          REPEAT_FIRST (resolve_tac ctxt @{thms analz_image_freshK_lemma}),
          ALLGOALS (asm_simp_tac (put_simpset Smartphone.analz_image_freshK_ss ctxt))])))\<close>
    "for proving the Session Key Compromise theorem"

method_setup possibility = \<open>
    Scan.succeed (fn ctxt =>
        SIMPLE_METHOD (Smartphone.possibility_tac ctxt))\<close>
    "for proving possibility theorems"

method_setup basic_possibility = \<open>
    Scan.succeed (fn ctxt =>
        SIMPLE_METHOD (Smartphone.basic_possibility_tac ctxt))\<close>
    "for proving possibility theorems"

lemma knows_subset_knows_Cons: "knows A evs \<subseteq> knows A (e # evs)"
by (induct e) (auto simp: knows_Cons)

(*Needed for actual protocols that will follow*)

declare legalUse_def [iff] illegalUse_def [iff]

end