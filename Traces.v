(*
The primary contribution of this file is to define the type `trace`
representing a trace of a program.

The function `program_traces` computes the traces of a program `p`.
The function `trace_eq` is equality for traces.

*)

From NITraces Require Import Program AssocList.

From Coq Require Import Lists.List Unicode.Utf8.
Import ListNotations.
  
Module Trace := AssocList Branch Bool.
Definition trace := Trace.t.

(* given a trace `tr` and trace list `trl`, return
each trace in `trl` with `tr` appended to its front *)
Fixpoint append_trace (tr : Trace.t) trl :=
  match trl with
  | [] => []
  | tr' :: trl_tail => (tr ++ tr') :: (append_trace tr trl_tail)
  end.

(* given two trace lists, return the list of traces that can be formed
by appending a trace from the former with a trace from the latter *)
Fixpoint append_trace_lists trl₁ trl₂ :=
  match trl₁ with
  | [] => []
  | tr :: trl₁_tail => append_trace tr trl₂ ++ append_trace_lists trl₁_tail trl₂
  end.

Fixpoint expression_traces e :=
  match e with
  | ⦃(_) = (_) ⊕[_] (_)⦄ => []
  | ⦃if[b] (_) then {{e₀}} else {{e₁}}⦄ =>
      (append_trace [(b, true)] (expression_traces e₀)) ++ (append_trace [(b, false)] (expression_traces e₁))
  | ⦃{e₀}; {e₁}⦄ => append_trace_lists (expression_traces e₀) (expression_traces e₁)
  end.

Definition program_traces (p : program) :=
  expression_traces (body p).





