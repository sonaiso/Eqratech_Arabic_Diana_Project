(** * FractalHub Code Extraction
    
    Extract verified Coq code to OCaml for integration with Python.
*)

Require Import FractalHub.Base.
Require Import FractalHub.Layers.
Require Import FractalHub.Trace.
Require Import FractalHub.Gates.
Require Import FractalHub.LockedArchitecture.
Require Import FractalHub.Invariants.

Require Extraction.
Extraction Language OCaml.

(** Configure extraction *)
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive nat => "int" ["0" "(fun x -> x + 1)"]
  "(fun fO fS n -> if n = 0 then fO () else fS (n-1))".
Extract Inductive string => "string" [""""""].

(** Extract main types *)
Extraction "fractalhub_kernel.ml" 
  Layer Form Meaning FourConditions Gate Trace
  valid_four_conditions valid_trace
  build_trace append_gate
  locked_architecture_holds.
