(*  Title:      Smartphone.thy
    Author:     Felipe Rodopoulos, University of Brasilia
    Copyright   2018  University of Brasilia

Theory for offline and out-of-band channels, defined by communications
  means created using the smartphone camera for decoding QR codes displayed
  at other insecure devices screens.

Definitions for keys, initial state of agents and smartphone's usability
*)

theory Smartphone imports "./EventSP" begin

axiomatization
  shrK  ::  "agent \<Rightarrow> key" and
  phnK  ::  "smartphone \<Rightarrow> key"

where
  inj_shrK : "inj shrK" and
  inj_phnK : "ink phnK"

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
    initState_Spy : "initState Spy = (Key`(range shrK) \<union> (Key` phnK` (badp \<inter> connected)))"
  end


end