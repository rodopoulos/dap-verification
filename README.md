# Formal Verification of the Dynamic Authorization Protocol

This repository presents my Master Thesis at University of Brasilia, done between the period of 2017 and 2019. It is a formal verification of a security protocol for reliable authorization of banking transaction in an insecure computer.

We use the Inductive Method approach in order to describe the protocol as a *formal protocol model*, inductively defined by its steps. Then, model correctness and protocol safety properties are verified through extensive analysis of model set rules, where a property of the set attempts to formalize some protocol goal.

Verification steps are defined as lemmas, where proofs are aided by Isabelle, given its nice support with inductively constructed sets and efficient simplification.

This is a work in progress, which will be probably the finalized in February 2019.
