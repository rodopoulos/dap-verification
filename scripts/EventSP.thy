(*  Title:      Smartphone.thy
    Author:     Felipe Rodopoulos, University of Brasilia
    Copyright   2018  University of Brasilia

Theory of Events for Security Protocol that use the offline and out-of-band
  channels defined by communications means created using the smartphone
  camera for decoding QR codes displayed at other insecure devices screens.

"badp" smartphones are compromised by the Spy; their private keys and internal
  stores are visible to her
*)

theory EventSP imports "~~/src/HOL/Auth/Message" "~~/src/HOL/Library/Simps_Case_Conv" begin

consts (* Initial states of agents -- parameter of the construction *)
  initState :: "agent => msg set"

datatype smartphone = Smartphone agent

datatype
  event = Says    agent agent msg
        | Notes   agent       msg
        | Gets    agent       msg
        | Scans   agent       smartphone msg (* Agent scans a message with her smartphone... *)
        | Gets_s  smartphone  msg (* ... smartphone receives it. *)
        | Outputs smartphone  agent msg (* Smartphone gives information to be inputed in agent... *)
        | Gets_a  agent       msg (* ... agent receives it. *)
        | Inputs  agent       smartphone msg (* Agent manually inputs data into smartphone *)

consts
  bad        :: "agent set"      (* compromised agents *)
  badp       :: "smartphone set" (* compromised smartphones *)
  stolen     :: "smartphone set" (* stolen smartphones *)

specification (bad)
  Spy_in_bad  [iff]: "Spy \<in> bad"
  Server_not_bad [iff]: "Server \<notin> bad"
  apply (rule exI [of _ "{Spy}"], simp)
  done

specification (stolen)
  Server_phone_not_stolen [iff]: "Smartphone Server \<notin> stolen"
  Spy_phone_not_stolen [iff]: "Smartphone Spy \<notin> stolen"
  Stolen_in_badp [iff] : "stolen \<subseteq> badp"
  apply blast
  done

specification (badp)
  (* Spy phone is secured because she already can use it freely *)
  Spy_phone_in_bad [iff]: "Smartphone Spy \<notin> badp"
  Server_phone_not_bad [iff]: "Smartphone Server \<notin> badp"
  apply blast
  done

(* Agents' knowledge definition over a trace is extended to comprehend new Smartphone events *)
primrec knows :: "agent \<Rightarrow> event list \<Rightarrow> msg set" where
  knows_Nil :  "knows A [] = initState A" |
  knows_Cons : "knows A (ev # evs) =
    (case ev of
      Says A' B X \<Rightarrow>
        if (A = A' | A = Spy) then insert X (knows A evs)
        else (knows A evs)

      | Notes A' X \<Rightarrow>
        if (A = A' | (A = Spy & A' \<in> bad)) then insert X (knows A evs)
        else knows A evs

      | Gets A' X \<Rightarrow>
        if (A = A' & A \<noteq> Spy) then insert X (knows A evs)
        else knows A evs

      | Scans A' P X \<Rightarrow>
        if (A = A') then insert X (knows A evs)
        else knows A evs

      (* Agents knowledge set is already enriched in Scans event.
         However, compromised smartphones disclose their secrets to the Spy *)
      | Gets_s P X \<Rightarrow>
        if (A = Spy & P \<in> badp) then insert X (knows A evs)
        else knows A evs

      | Outputs P A' X \<Rightarrow>
        if (A = A' | (A = Spy & P \<in> badp)) then insert X (knows A evs)
        else knows A evs

      | Gets_a A' X \<Rightarrow>
        if (A = A' & A \<noteq> Spy) then insert X (knows A evs)
        else knows A evs

      | Inputs A' P X \<Rightarrow>
        if (A = A') then insert X (knows A evs)
        else knows A evs
  )"


primrec used :: "event list \<Rightarrow> msg set" where
  used_Nil  : "used [] = (\<Union> B. parts (initState B))" |
  used_Cons : "used (ev # evs) =
    (case ev of
        Says A B X \<Rightarrow> parts {X} \<union> (used evs)
      | Notes A X \<Rightarrow> parts {X} \<union> (used evs)
      | Gets A X \<Rightarrow> used evs
      | Scans A P X \<Rightarrow> parts {X} \<union> used evs
      (* We need to extend the used set here due to lemma parts_knows_Spy_subset_used
         We do not violate the reception invariant, since every message received here was already
         been added in the above definition *)
      | Gets_s P X \<Rightarrow> parts {X} \<union> used evs
      | Outputs P A X \<Rightarrow> parts {X} \<union> used evs
      | Gets_a A X \<Rightarrow> used evs
      | Inputs A P X \<Rightarrow> parts {X} \<union> used evs
  )"

(* Describing how some the set used evs is enriched given our events *)
lemma Notes_imp_used [rule_format] :
  "Notes A X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split)
done

lemma Says_imp_used [rule_format] :
  "Says A B X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split)
done

lemma Scans_imp_used [rule_format] :
  "Scans A P X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split)
done

lemma Outputs_imp_used [rule_format] :
  "Outputs P A X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split)
done

lemma Getss_imp_Scans:
  "Gets_s P X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split)
done

lemma Inputs_imp_Scans:
  "Inputs A P X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split)
done


(* AGENTS' KNOWLEDGE LEMMAS *)
(* Simplifying:
   parts(insert X (knows Spy evs)) = parts{X} \<union> parts(knows Spy evs) *)
lemmas parts_insert_knows_A = parts_insert [of _ "knows A evs"] for A evs

lemma knows_Spy_Says [simp] :
  "knows Spy (Says A B X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Gets [simp] :
  "knows Spy (Gets B X # evs) = knows Spy evs"
by simp

lemma knows_Spy_Notes [simp] :
  "knows Spy (Notes A X # evs) =
    (if A \<in> bad then insert X (knows Spy evs)
     else knows Spy evs)"
by simp

lemma knows_Spy_Scans [simp] :
  "knows Spy (Scans A P X # evs) =
    (if A = Spy then insert X (knows Spy evs)
     else knows Spy evs)"
by simp

lemma knows_Spy_Gets_s [simp] :
  "knows Spy (Gets_s P X # evs) =
    (if P \<in> badp then insert X (knows Spy evs)
     else knows Spy evs)"
by simp

lemma knows_Spy_Outputs [simp] :
  "knows Spy (Outputs P A X # evs) =
    (if A = Spy then insert X (knows Spy evs)
     else if P \<in> badp then insert X (knows Spy evs)
     else knows Spy evs)"
by simp

lemma knows_Spy_Gets_a [simp] :
  "knows Spy (Gets_a A X # evs) = knows Spy evs"
by simp

lemma knows_Spy_Inputs [simp] :
  "knows Spy (Inputs A P X # evs) = 
    (if A = Spy then insert X (knows Spy evs)
     else knows Spy evs)"
by simp


lemma knows_Spy_subset_knows_Spy_Says :
  "knows Spy evs \<subseteq> knows Spy (Says A B X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Notes :
  "knows Spy evs \<subseteq> knows Spy (Notes A X # evs)"
by force

lemma knows_Spy_subset_knows_Spy_Gets :
  "knows Spy evs \<subseteq> knows Spy (Gets A X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Scans :
  "knows Spy evs \<subseteq> knows Spy (Scans A P X # evs)"
by auto

lemma knows_Spy_subset_knows_Spy_Gets_s :
  "knows Spy evs \<subseteq> knows Spy (Gets_s P X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Outputs :
  "knows Spy evs \<subseteq> knows Spy (Outputs P A X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Gets_a :
  "knows Spy evs \<subseteq> knows Spy (Gets_a A X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Inputs :
  "knows Spy evs \<subseteq> knows Spy (Inputs A P X # evs)"
by (simp add: subset_insertI)


lemma Says_imp_knows_Spy [rule_format] :
  "Says A B X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all split: event.split)
done

lemma Notes_imp_knows_Spy [rule_format] :
  "Notes A X \<in> set evs \<longrightarrow> A \<in> bad \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done

lemma Scans_imp_knows_Spy [rule_format] :
  "Scans Spy P X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done

lemma Gets_s_imp_knows_Spy_by_smartphone [rule_format] :
  "Gets_s P X \<in> set evs \<longrightarrow> P \<in> badp \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done

lemma Outputs_imp_knows_Spy [rule_format] :
  "Outputs P Spy X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done

lemma Outputs_imp_knows_Spy_by_smartphone [rule_format] :
  "Outputs P A X \<in> set evs \<longrightarrow> P \<in> badp \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done

lemma Inputs_imp_knows_Spy [rule_format] :
  "Inputs Spy P X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done


lemmas knows_Spy_partsEs =
     Says_imp_knows_Spy [THEN parts.Inj, elim_format]
     parts.Body [elim_format]

lemma knows_Says: "knows A (Says A B X # evs) = insert X (knows A evs)"
by simp

lemma knows_Notes: "knows A (Notes A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Gets:
  "A \<noteq> Spy \<longrightarrow> knows A (Gets A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Scans: "knows A (Scans A C X # evs) = insert X (knows A evs)"
by simp

lemma knows_Gets_s:
  "A \<noteq> Spy \<longrightarrow> knows A (Gets_s C X # evs) = knows A evs"
by simp

lemma knows_Outputs:
  "knows A (Outputs C A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Gets_a:
  "A \<noteq> Spy \<longrightarrow> knows A (Gets_a A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Inputs:
  "knows A (Inputs A P X # evs) = insert X (knows A evs)"
by simp


lemma knows_subset_knows_Says: "knows A evs \<subseteq> knows A (Says A' B X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Notes: "knows A evs \<subseteq> knows A (Notes A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Gets: "knows A evs \<subseteq> knows A (Gets A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Scans: "knows A evs \<subseteq> knows A (Scans A' P X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Gets_s: "knows A evs \<subseteq> knows A (Gets_s P X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Outputs: "knows A evs \<subseteq> knows A (Outputs P A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Gets_a: "knows A evs \<subseteq> knows A (Gets_a A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Inputs: "knows A evs \<subseteq> knows A (Inputs A' P X # evs)"
by (simp add: subset_insertI)


(* Agents know what they say *)
lemma Says_imp_knows [rule_format] :
  "Says A B X \<in> set evs \<longrightarrow> X \<in> knows A evs"
  apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply auto
done

(* Agents know what they note *)
lemma Notes_imp_knows [rule_format] :
  "Notes A X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply auto
done

(* Agents know what they receive *)
lemma Gets_imp_knows [rule_format] :
  "A \<noteq> Spy \<longrightarrow> Gets A X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done

(* Agents know what their smartphone scans *from them* *)
lemma Scans_imp_knows [rule_format] :
  "Scans A P X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply auto
done

(* Agents know what they input to their smartphone *)
lemma Inputs_imp_knows [rule_format] :
  "Inputs A P X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply auto
done


(* Agents do NOT know what they smartphones reads... *)
(* So no rule for this *)

(* Agents knows what their smartphones shows to them *)
lemma Outputs_imp_knows [rule_format] :
  "Outputs P A X \<in> set evs \<longrightarrow> X \<in> knows A evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply auto
done



(* REMEMBER: knows (Spy evs) = everything that appeared in the trace so far *)
(* Everything that appeared in the trace is not fresh *)
lemma parts_knows_Spy_subset_used :
  "parts (knows Spy evs) \<subseteq> used evs"
apply (induct_tac "evs", force)
apply (simp add: parts_insert_knows_A split: event.split)
apply (auto)
done

lemmas usedI = parts_knows_Spy_subset_used [THEN subsetD, intro]

lemma initState_into_used :
  "X \<in> parts (initState B) ==> X \<in> used evs"
apply (induct_tac "evs")
apply (simp_all add: parts_insert_knows_A split: event.split, blast)
done

simps_of_case used_Cons_simps [simp]: used_Cons



(* USED FUNCTION LEMMAS *)
lemma Says_parts_used [rule_format (no_asm)] :
  "Says A B X \<in> set evs \<longrightarrow> (parts {X}) \<subseteq> used evs "
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply (auto)
done

lemma Notes_parts_used [rule_format (no_asm)] :
  "Notes A X \<in> set evs \<longrightarrow> (parts {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply (auto)
done

lemma Scans_parts_used [rule_format (no_asm)] :
  "Scans A P X \<in> set evs \<longrightarrow> (parts {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply (auto)
done

lemma Gets_s_parts_used [rule_format (no_asm)] :
  "Gets_s P X \<in> set evs \<longrightarrow> (parts {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply (auto)
done

lemma Outputs_parts_used [rule_format (no_asm)] :
  "Outputs P A X \<in> set evs \<longrightarrow> (parts {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply (auto)
done

lemma Inputs_parts_used [rule_format (no_asm)] :
  "Inputs A P X \<in> set evs \<longrightarrow> (parts {X}) \<subseteq> used evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply (auto)
done



declare knows_Cons [simp del]
        used_Nil [simp del]
        used_Cons [simp del]

lemma knows_subset_knows_Cons :
  "knows A evs \<subseteq> knows A (e # evs)"
by (induct e, auto simp: knows_Cons)

lemma initState_subset_knows :
  "initState A \<subseteq> knows A evs"
apply (induct_tac evs, simp)
apply (blast intro: knows_subset_knows_Cons [THEN subsetD])
done

text\<open>For proving \<open>new_keys_not_used\<close>\<close>

lemma keysFor_parts_insert:
     "\<lbrakk> K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) \<rbrakk>
      \<Longrightarrow> K \<in> keysFor (parts (G \<union> H)) \<or> Key (invKey K) \<in> parts H"
by (force
    dest!: parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
           analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD]
    intro: analz_subset_parts [THEN subsetD] parts_mono [THEN [2] rev_subsetD])

end