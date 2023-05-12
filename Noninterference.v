(*
This file provides definitions of noninterference and trace noninterference with respect
to the big step semantics from Semantics.v and paramterized over equivalence relations
on the input and output memory states. Input and output memory states are both (stack, heap)
pairs as also defined in Semantics.v.
*)

From NITraces Require Import Program Traces AssocList Semantics.

From Coq Require Import Lists.List Unicode.Utf8.
Import ListNotations.

Section MainDefinitions.
  Context (in_equiv : memory → memory → Prop).
  Context (out_equiv : memory → memory → Prop).

  Infix "≡ᵢ" := in_equiv (at level 50).
  Infix "≡ₒ" := out_equiv (at level 50).

  (* classical noninterference *)
  Definition noninterferent (p : program) :=
    let e := body p in
    ∀ mᵢ mᵢ' mₒ mₒ',
      (mᵢ ≡ᵢ mᵢ') →
      ⟨e; mᵢ ↓ mₒ⟩ →
      ⟨e; mᵢ' ↓ mₒ'⟩ →
      (mₒ ≡ₒ mₒ').

  (* trace noninterference *)
  Definition trace_noninterference (p : program) (t : trace) :=
    let e := body p in
    ∀ mᵢ mᵢ' mₒ mₒ',
      (mᵢ ≡ᵢ mᵢ') →
      ⟨e; mᵢ ↓ mₒ; t⟩ →
      ⟨e; mᵢ' ↓ mₒ'⟩ →
      (mₒ ≡ₒ mₒ').

End MainDefinitions.
