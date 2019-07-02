(*  Title:      Smartphone.thy
    Author:     Felipe Rodopoulos, University of Brasilia
    Copyright   2018  University of Brasilia

Theory of Events for Security Protocol that use the offline and out-of-band
  channels defined by communications means created using the smartphone
  camera for decoding QR codes displayed at other insecure devices screens.

"badP" smartphones are compromised by the Spy; their private keys and internal
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
        | Scans   agent       smartphone msg (* Agent scans a message with her smartphone and ... *)
        | SGets  smartphone  msg (* ... smartphone receives it. *)
        | Shows smartphone  agent msg (* Smartphone shows information to its agent and ... *)
        | AGets  agent       msg (* ... agent receives it. *)
        | Inputs  agent       smartphone msg (* Agent manually inputs data into smartphone *)

consts
  bad        :: "agent set"      (* compromised agents *)
  badP       :: "smartphone set" (* compromised smartphones *)
  stolen     :: "smartphone set" (* stolen smartphones *)
  secureP    :: "bool" (* assumption of secure smartphones, inviolable by the Spy *)

abbreviation
  insecureP :: bool where (* certain protocols make no assumption of secure smartphones *)
    "insecureP == \<not>secureP"

specification (bad)
  Spy_in_bad     [iff]: "Spy \<in> bad"
  Server_not_bad [iff]: "Server \<notin> bad"
  apply (rule exI [of _ "{Spy}"], simp)
done

specification (badP)
  (* Spy phone is secured because she already can use it freely *)
  Spy_phone_not_badP     [iff]: "Smartphone Spy \<notin> badP"
  Server_phone_not_badP [iff]: "Smartphone Server \<notin> badP"
  apply blast
done

specification (stolen)
  Server_phone_not_stolen [iff]: "Smartphone Server \<notin> stolen"
  Spy_phone_not_stolen    [iff]: "Smartphone Spy \<notin> stolen"
  Stolen_in_badP [iff] : "stolen \<subseteq> badP"
  apply blast
done

(* Agents' knowledge definition over a trace is extended to comprehend new Smartphone events *)
primrec knows :: "agent \<Rightarrow> event list \<Rightarrow> msg set" where
  knows_Nil :  "knows A [] = initState A" |
  knows_Cons : "knows A (ev # evs) =
    (case ev of
      \<comment> \<open>An agent knows what he sends to anyone. The Spy knows everything sent on a trace\<close>
      Says A' B X \<Rightarrow>
        if (A = A' | A = Spy) then insert X (knows A evs)
        else (knows A evs)

      \<comment> \<open>An agent knows what he notes. The Spy knows what compromised agents knows on a trace\<close>
      | Notes A' X \<Rightarrow>
        if (A = A' | (A = Spy & A' \<in> bad)) then insert X (knows A evs)
        else knows A evs

      \<comment> \<open>An agent, except the Spy, knows what she receives in a trace. Due to the Says event and
      reception invariant, the Spy knowledge does not need to be extended\<close>
      | Gets A' X \<Rightarrow>
        if (A = A' & A \<noteq> Spy) then insert X (knows A evs)
        else knows A evs

      \<comment> \<open>An agent knows what she shows to her smartphone to scan. The Spy knows what a compromised
         agent shows to her smartphones to scan\<close>
      | Scans A' P X \<Rightarrow>
        if (A = A' | (A = Spy & A' \<in> bad)) then insert X (knows A evs)
        else knows A evs

      \<comment> \<open>Due to reception invariant of Scans event, an agent does not enrich her knowledge set 
         from what her smartphone receives\<close>
      | SGets P X \<Rightarrow> 
        if secureP then knows A evs
        \<comment> \<open>However, if devices can be compromised, the Spy knows what a compromised phone receives\<close>
        else
          if (A = Spy & P \<in> badP) then insert X (knows A evs)
          else knows A evs

      \<comment> \<open>An agent, including the Spy, knows what her smartphone shows to her\<close>
      | Shows P A' X \<Rightarrow>
        if secureP then
          if (A = A') then insert X (knows A evs)
          else knows A evs
        \<comment> \<open>When insecure devices hold, the Spy knows what compromised devices shows\<close>
        else 
          if (A = Spy & P \<in> badP) then insert X (knows A evs)
          else knows A evs

      \<comment> \<open>An agent knows what she receives from her smartphone. The Spy already knows from the previous event\<close>
      | AGets A' X \<Rightarrow>
        if (A = A' & A \<noteq> Spy) then insert X (knows A evs)
        else knows A evs

      \<comment> \<open>An agent, and only her, knows what she manually inputs to her smartphone\<close>
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
      | SGets P X \<Rightarrow> parts {X} \<union> used evs
      | Shows P A X \<Rightarrow> parts {X} \<union> used evs
      | AGets A X \<Rightarrow> used evs
      | Inputs A P X \<Rightarrow> parts {X} \<union> used evs
  )"

text\<open>Describing how some the set used evs is enriched given our events\<close>
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

lemma Shows_imp_used [rule_format] :
  "Shows P A X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split)
done

lemma Inputs_imp_used :
  "Inputs A P X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split)
done

section\<open>Function \<^term>\<open>knows\<close>\<close>
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
    (if A \<in> bad then insert X (knows Spy evs)
     else knows Spy evs)"
by simp

lemma knows_Spy_SGets_secureP [simp] :
  "secureP \<Longrightarrow> knows Spy (SGets P X # evs) = knows Spy evs"
by simp

lemma knows_Spy_SGets_insecureP [simp] :
  "insecureP \<Longrightarrow> knows Spy (SGets P X # evs) = 
    (if (P \<in> badP) then insert X (knows Spy evs)
    else knows Spy evs)"
by simp

lemma knows_Spy_Shows_secureP [simp] :
  "secureP \<Longrightarrow> knows Spy (Shows P A X # evs) =
    (if A = Spy then insert X (knows Spy evs)
     else knows Spy evs)"
by simp

lemma knows_Spy_Shows_insecureP [simp] :
  "insecureP \<Longrightarrow> knows Spy (Shows P A X # evs) =
    (if P \<in> badP then insert X (knows Spy evs)
     else knows Spy evs)"
by simp

lemma knows_Spy_AGets [simp] :
  "knows Spy (AGets A X # evs) = knows Spy evs"
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

lemma knows_Spy_subset_knows_Spy_SGets :
  "knows Spy evs \<subseteq> knows Spy (SGets P X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Shows :
  "knows Spy evs \<subseteq> knows Spy (Shows P A X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_AGets :
  "knows Spy evs \<subseteq> knows Spy (AGets A X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Inputs :
  "knows Spy evs \<subseteq> knows Spy (Inputs A P X # evs)"
by (simp add: subset_insertI)


lemma Says_imp_knows_Spy [rule_format (no_asm)] :
  "Says A B X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"

  apply (induct_tac "evs")
  apply (simp_all split: event.split)
done

lemma Notes_imp_knows_Spy [rule_format (no_asm)] :
  "Notes A X \<in> set evs \<longrightarrow> A \<in> bad \<longrightarrow> X \<in> knows Spy evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
done

\<comment> \<open>Nothing can be stated about Gets event\<close>

lemma Scans_imp_knows_Spy [rule_format (no_asm)] :
  "Scans A P X \<in> set evs \<longrightarrow> A \<in> bad \<longrightarrow> X \<in> knows Spy evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
done

\<comment> \<open>Nothing can be stated on a SGets when phones are secured event\<close>
lemma SGets_imp_knows_Spy_insecureP [rule_format (no_asm)] :
  "SGets P X \<in> set evs \<longrightarrow> (insecureP \<and> P \<in> badP) \<longrightarrow> X \<in> knows Spy evs" 

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
done

lemma Shows_imp_knows_Spy_secureM [rule_format (no_asm)] :
  "Shows P Spy X \<in> set evs \<longrightarrow> secureP \<longrightarrow> X \<in> knows Spy evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
done

lemma Shows_imp_know_Spy_insecureM [rule_format (no_asm)] :
  "Shows P A X \<in> set evs \<longrightarrow> (insecureP \<and> P \<in> badP) \<longrightarrow> X \<in> knows Spy evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
done

\<comment> \<open>Nothing can be stated here on a AGets event\<close>
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

lemma knows_Scans: "knows A (Scans A P X # evs) = insert X (knows A evs)"
by simp

lemma knows_SGets:
  "A \<noteq> Spy \<longrightarrow> knows A (SGets P X # evs) = knows A evs"
by simp

lemma knows_Shows_secureP:
  "secureP \<longrightarrow> knows A (Shows P A X # evs) = insert X (knows A evs)"
by simp

lemma knows_Shows_insecureP:
  "(insecureP \<and> A \<noteq> Spy) \<longrightarrow> knows A (Shows P A X # evs) = knows A evs"
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

lemma knows_subset_knows_SGets: "knows A evs \<subseteq> knows A (SGets P X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Shows: "knows A evs \<subseteq> knows A (Shows P A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_AGets: "knows A evs \<subseteq> knows A (AGets A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Inputs: "knows A evs \<subseteq> knows A (Inputs A' P X # evs)"
by (simp add: subset_insertI)

\<comment> \<open>Agents know what they say\<close>
lemma Says_imp_knows [rule_format] :
  "Says A B X \<in> set evs \<longrightarrow> X \<in> knows A evs"
  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
  apply (auto)
done

\<comment> \<open>Agents know what they note\<close>
lemma Notes_imp_knows [rule_format] :
  "Notes A X \<in> set evs \<longrightarrow> X \<in> knows A evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
  apply (auto)
done

\<comment> \<open>Agents know what they receive\<close>
lemma Gets_imp_knows [rule_format] :
  "A \<noteq> Spy \<longrightarrow> Gets A X \<in> set evs \<longrightarrow> X \<in> knows A evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
done

\<comment> \<open>Agents know what their smartphone scans\<close>
lemma Scans_imp_knows [rule_format] :
  "Scans A (Smartphone A) X \<in> set evs \<longrightarrow> X \<in> knows A evs"
  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
  apply (auto)
done

\<comment> \<open>Agents know what they input to their smartphone\<close>
lemma Inputs_imp_knows [rule_format] :
  "Inputs A (Smartphone A) X \<in> set evs \<longrightarrow> X \<in> knows A evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
  apply (auto)
done

\<comment> \<open>Agents do not know what they smartphones reads...\<close>

\<comment> \<open>Agents know what their smartphones shows to them, if the device are secured\<close>
lemma Shows_imp_knows_secureP [rule_format] :
  "secureP \<longrightarrow> Shows (Smartphone A) A X \<in> set evs \<longrightarrow> X \<in> knows A evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
done

lemma Shows_imp_knows_insecureP [rule_format] :
  "(insecureP \<and> (Smartphone A) \<in> badP) \<longrightarrow> Shows (Smartphone A) A X \<in> set evs \<longrightarrow> X \<in> knows Spy evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
done

\<comment> \<open>Agents know what they receive from a smartphone\<close>
lemma AGets_imp_knows [rule_format] :
  "A \<noteq> Spy \<longrightarrow> AGets A X \<in> set evs \<longrightarrow> X \<in> knows A evs"

  apply (induct_tac "evs")
  apply (simp_all (no_asm_simp) split: event.split)
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

section\<open>Function \<^term>\<open>used\<close>\<close>
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

lemma Shows_parts_used [rule_format (no_asm)] :
  "Shows P A X \<in> set evs \<longrightarrow> (parts {X}) \<subseteq> used evs"
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

lemma keysFor_parts_insert:
     "\<lbrakk> K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) \<rbrakk>
      \<Longrightarrow> K \<in> keysFor (parts (G \<union> H)) \<or> Key (invKey K) \<in> parts H"
by (force
    dest!: parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
           analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD]
    intro: analz_subset_parts [THEN subsetD] parts_mono [THEN [2] rev_subsetD])

end