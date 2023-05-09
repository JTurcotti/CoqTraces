(*
The primary contribution of this file is the definition of the stack and heap types,
which includes the definitions of the _values_ used in them, in service of defining
the big step operational semantics for our programs from Program.v. Because unequal
trace, stack, and heap values can be semantically considered equal, the big step
semantics contains a case for deriving across known semantic equality such as `mem_eq`.

Also of note in this file is the function `eval_branch_in_memory` - it is responsible
for checking whether a given branch on a given variable in a given memory state
should be taken in the true or false direction - a key component of our semantics

 *)

From NITraces Require Import Program Traces AssocList.

From Coq Require Import Lists.List Unicode.Utf8.
Import ListNotations.

(* base values are the core set of values that stack variables can take -
   modeled as integers *)
Inductive base_value := BaseValue (n : nat).

(* module-ize *)
Module BaseValue.
  Definition t := base_value.
  Definition eq := @eq t.
  Definition eq_dec : ∀ (x x' : t), {eq x x'} + {~eq x x'}.
  Proof.
    unfold eq.
    decide equality.
    apply PeanoNat.Nat.eq_dec.
  Defined.
End BaseValue.

(* values themselves are the base values closed over the set of operators -
   since there are no equalities or other properties of these operators,
   values are equavalent to syntax trees *)
Inductive value :=
| One : base_value → value
| Composite : value → operator → value → value.

(* notation for lifting base values to values *)
Notation "⦇ bv ⦈" := (One bv).
Notation "⦇ v₀ ⊕ [ op ] v₁ ⦈" := (Composite v₀ op v₁).

(* the following definitions provide a non-duplicating append operation
on lists of base values *)

Definition nodup_val_cons (v : base_value) (lv : list base_value) :=
  if (List.in_dec BaseValue.eq_dec v lv) then lv else v :: lv.

Fixpoint nodup_val_app (lv₀ lv₁ : list base_value) :=
  match lv₀ with
  | [] => lv₁
  | v :: lv₀_tail => nodup_val_app lv₀_tail (nodup_val_cons v lv₁)
  end.

Lemma nodup_val_app_sound : ∀ lv₀ lv₁,
    (NoDup lv₀) → (NoDup lv₁) → (NoDup (nodup_val_app lv₀ lv₁)).
Admitted.

(* reduce a value to a non-duplicated list of underlying base values *)
Fixpoint flatten_vals (v : value) : list base_value :=
  match v with
  | ⦇ bv ⦈ => [bv]
  | ⦇ v₀ ⊕[_] v₁ ⦈ => nodup_val_app (flatten_vals v₀) (flatten_vals v₁)
  end.

(* module-ize *)
Module Value.
  Definition t := value.
  Definition eq := @eq t.
  Definition eq_dec : ∀ (x x' : t), {eq x x'} + {~eq x x'}.
  Proof.
    unfold eq.
    decide equality.
    apply BaseValue.eq_dec.
    apply Op.eq_dec.
  Defined.
End Value.
(* a stack maps stack variables (defined in Program.v) to values *)
Module Stack := AssocList Var Value.

(* lists of branches are equal if they contain the same elements *)
Module BranchList.
  Definition t := list branch.
  Definition eq lb₁ lb₂ := ∀ b : branch, (In b lb₁) ↔ (In b lb₂).
  Definition eq_dec : ∀ (x x' : t), {eq x x'} + {~eq x x'}.
    Admitted.
End BranchList.

(* a heap maps the base values to their "interpretations" - the
   interpretation for a base value is the direction that it causes
   each branch to take if it is inspected in that branch's guard
   (hence - it is a vector of size equal to the number of branches).
   The underlying storage for these vectors is sparse - it is a set of
   their one components.  In the case that multiple values are
   inspected in a given guard, the xor of the individual components
   for each value is taken as the value that determines the direction
   the branch will be taken. *)
Module Heap := AssocList BaseValue BranchList.

(* memory consists of a stack and a heap *)
Definition memory : Type := Stack.t * Heap.t.

(* semantic equality for memory states *)
Definition mem_eq (m₁ m₂ : memory) :=
  let (σ₁, ρ₁) := m₁ in
  let (σ₂, ρ₂) := m₂ in
  Stack.eq σ₁ σ₂ ∧ Heap.eq ρ₁ ρ₂.
                           
(* this is VERY important - *)

Lemma branch_eq_dec : ∀ v₀ v₁ : branch, {v₀ = v₁} + {v₀ ≠ v₁}.
  decide equality.
  apply PeanoNat.Nat.eq_dec.
Qed.

(* this function looks up each base_value in the passed list in the passed heap. If all
lookups succeed, Some is returned with the result of the lookups. Otherwise None is returned *)
Fixpoint lookup_in_heap (ρ : Heap.t) (lb : list base_value) : option (list (list branch)) :=
  match lb with
  | [] => Some []
  | bv :: lb_tail =>
      match (Heap.lookup ρ bv, lookup_in_heap ρ lb_tail) with
      | (Some looked_up_bv, Some looked_up_lb_tail) => Some (looked_up_bv :: looked_up_lb_tail)
      | _ => None
      end
  end.

(* this proposition encodes the fact that the branch `b`, which has as guard variable `x`,
will take direction `dir` in memory state `m`. This is the most important aspect of our
semantics. In particular, each base_value that was involved in the computation of `x`
is looked up in the heap, and the `b`th component of the bitstring found for each
heap lookup is xor'd together. This ensures each value has influence on the branch
direction.
*)
Definition eval_branch_in_memory (b : branch) (x : variable) (m : memory) (dir : bool) : Prop :=
  let (σ, ρ) := m in
  ∃ v, (Stack.contains σ x v) ∧
         let base_vals := flatten_vals v in
         match (lookup_in_heap ρ base_vals) with
         | None => False
         | Some base_val_bitstrings  =>
             let project bitstring :=
               if List.in_dec Branch.eq_dec b bitstring then true else false
             in
             (List.fold_right (fun bitstring => xorb (project bitstring))
                false base_val_bitstrings) = dir
         end.


Definition ε : trace := nil.

Notation "[ l ; a ↦ b ]" := ((a, b) :: l) (at level 50).

Reserved Notation "⟨ e ; m₀ ↓ m₁ ; t ⟩" (at level 50).

Inductive eval_with_trace : expression → memory → memory → trace → Prop :=
(* the EquivEval constructor generalizes the eval relation across equal arguments *)
| EquivEval : ∀ e m₀ m₀' m₁ m₁' t t',
    ⟨e ; m₀ ↓ m₁ ; t⟩ →
    (mem_eq m₀ m₀') →
    (mem_eq m₁ m₁') →
    (Trace.eq t t') →
    ⟨e; m₀' ↓ m₁' ; t'⟩
(* the AssignEval constructor evaluates assignments by looking up both operands in the stack,
and mapping the assigned value in the stack to the syntactically provided operator
applies to the values of the operands *)
| AssignEval : ∀ σ ρ x₀ x₁ x₂ v₁ v₂ o,
    (Stack.contains σ x₁ v₁) →
    (Stack.contains σ x₂ v₂) →
    ⟨⦃(x₀) = (x₁) ⊕[o] (x₂)⦄; (σ, ρ) ↓ ([σ ; x₀ ↦ ⦇v₁ ⊕[o] v₂⦈], ρ); ε⟩
(* the BranchEval rules evaluate branches by checking their guard
using the eval_branch_in_memory prop, and then sequencing
the true or false branch to get a new memory state that additionally
 has the direction of this branch noted in its guard *)                  
| BranchEvalTrue : ∀ σ ρ σ' ρ' x b e₀ e₁ t,
    (eval_branch_in_memory b x (σ, ρ) true) →
    ⟨e₀; (σ, ρ) ↓ (σ', ρ'); t⟩ →
    ⟨⦃if[b] (x) then {{e₀}} else {{e₁}}⦄; (σ, ρ) ↓ (σ', ρ'); [t; b ↦ true]⟩
| BranchEvalFalse : ∀ σ ρ σ' ρ' x b e₀ e₁ t,
    (eval_branch_in_memory b x (σ, ρ) true) →
    ⟨e₀; (σ, ρ) ↓ (σ', ρ'); t⟩ →
    ⟨⦃if[b] (x) then {{e₀}} else {{e₁}}⦄; (σ, ρ) ↓ (σ', ρ'); [t; b ↦ true]⟩
(* the SeqEval rule sequences the evaluation of two expression as expected,
 only interesting part is that traces get appended*)
| SeqEval : ∀ m₀ m₁ m₂ e₀ e₁ t₀ t₁,
    ⟨e₀; m₀ ↓ m₁; t₀⟩ →
    ⟨e₁; m₁ ↓ m₂; t₁⟩ →
    ⟨⦃{e₀}; {e₁}⦄; m₀ ↓ m₂; t₀ ++ t₁⟩
where "⟨ e ; m₀ ↓ m₁ ; t ⟩" := (eval_with_trace e m₀ m₁ t).

(* this is a version of the evaluation relation that discards information about traces *)
Definition eval (e : expression) (m₀ m₁ : memory) : Prop := ∃ t, ⟨e; m₀ ↓ m₁; t⟩.

Notation "⟨ e ; m₀ ↓ m₁ ⟩" := (eval e m₀ m₁) (at level 50).

(*TODO: write some examples testing the semantics *)


