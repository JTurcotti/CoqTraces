(*
The primary contribution of this file is to define the type `program`.

A `program` is an expression in the simple language defined below by the
inductive `expression` type - accompanied by a proof of well-formedness
showing that the numbers identifying branches and operators are unique.

This file also contains Notation declarations for pretty-typing expressions,
and a function `make_program` for converting expressions to programs by
re-numbering their operators and branches.

TODO: prove `make_program` sound via the lemma `make_wf_expression_top_sound`
*)




From Coq Require Import Unicode.Utf8 Strings.String.

Inductive branch := Branch (n : nat).
Definition default_branch := Branch 0.
Inductive variable := Var (s : string).
Inductive operator := Op (n : nat).
Definition default_op := Op 0.

(* TODO: add assignments like x = y that don't involve a binop *)
Inductive expression :=
| OpExp : variable → variable → operator → variable → expression
| BranchExp : branch → variable → expression → expression → expression
| SeqExp : expression → expression → expression.

Open Scope string_scope.

Declare Custom Entry var_entry.
(* \([^ ]+\) → Notation "'\1'" := (Var "\1") (in custom var_entry at level 0).
 *)
Notation "'a'" := (Var "a") (in custom var_entry at level 0).
Notation "'b'" := (Var "b") (in custom var_entry at level 0).
Notation "'c'" := (Var "c") (in custom var_entry at level 0).
Notation "'d'" := (Var "d") (in custom var_entry at level 0).
Notation "'e'" := (Var "e") (in custom var_entry at level 0).
Notation "'f'" := (Var "f") (in custom var_entry at level 0).
Notation "'g'" := (Var "g") (in custom var_entry at level 0).
Notation "'h'" := (Var "h") (in custom var_entry at level 0).
Notation "'i'" := (Var "i") (in custom var_entry at level 0).
Notation "'j'" := (Var "j") (in custom var_entry at level 0).
Notation "'k'" := (Var "k") (in custom var_entry at level 0).
Notation "'l'" := (Var "l") (in custom var_entry at level 0).
Notation "'m'" := (Var "m") (in custom var_entry at level 0).
Notation "'n'" := (Var "n") (in custom var_entry at level 0).
Notation "'o'" := (Var "o") (in custom var_entry at level 0).
Notation "'p'" := (Var "p") (in custom var_entry at level 0).
Notation "'q'" := (Var "q") (in custom var_entry at level 0).
Notation "'r'" := (Var "r") (in custom var_entry at level 0).
Notation "'s'" := (Var "s") (in custom var_entry at level 0).
Notation "'t'" := (Var "t") (in custom var_entry at level 0).
Notation "'u'" := (Var "u") (in custom var_entry at level 0).
Notation "'v'" := (Var "v") (in custom var_entry at level 0).
Notation "'w'" := (Var "w") (in custom var_entry at level 0).
Notation "'x'" := (Var "x") (in custom var_entry at level 0).
Notation "'y'" := (Var "y") (in custom var_entry at level 0).
Notation "'z'" := (Var "z") (in custom var_entry at level 0).

Notation "'x₀'" := (Var "x₀") (in custom var_entry at level 0).
Notation "'x₁'" := (Var "x₁") (in custom var_entry at level 0).
Notation "'x₂'" := (Var "x₂") (in custom var_entry at level 0).
Notation "'x₃'" := (Var "x₃") (in custom var_entry at level 0).
Notation "'y₀'" := (Var "y₀") (in custom var_entry at level 0).
Notation "'y₁'" := (Var "y₁") (in custom var_entry at level 0).
Notation "'y₂'" := (Var "y₂") (in custom var_entry at level 0).
Notation "'y₃'" := (Var "y₃") (in custom var_entry at level 0).
Notation "'t₀'" := (Var "t₀") (in custom var_entry at level 0).
Notation "'t₁'" := (Var "t₁") (in custom var_entry at level 0).
Notation "'t₂'" := (Var "t₂") (in custom var_entry at level 0).
Notation "'t₃'" := (Var "t₃") (in custom var_entry at level 0).
Notation "'ret'" := (Var "ret") (in custom var_entry at level 0).
Notation "'in'" := (Var "in") (in custom var_entry at level 0).
Notation "'out'" := (Var "out") (in custom var_entry at level 0).

Notation "( x )" := (x) (in custom var_entry at level 0, x constr at level 0).


Declare Custom Entry expression_entry.
Notation "x₀ = x₁ ⊕ x₂" := (OpExp x₀ x₁ default_op x₂)
                             (in custom expression_entry at level 1,
                                 x₀ custom var_entry at level 0, x₁ custom var_entry at level 0, x₂ custom var_entry at level 0).
Notation "x₀ = x₁ ⊕ [ op ] x₂" := (OpExp x₀ x₁ op x₂)
                                    (in custom expression_entry at level 1,
                                        op constr at level 0,
                                        x₀ custom var_entry at level 0,
                                        x₁ custom var_entry at level 0, x₂ custom var_entry at level 0).

Notation "'if' x₀ 'then' { e₀ } 'else' { e₁ }" := (BranchExp default_branch x₀ e₀ e₁)
                                                    (in custom expression_entry at level 1,
                                                        x₀ custom var_entry at level 0,
                                                        e₀ custom expression_entry at level 0, e₁ custom expression_entry at level 0).
Notation "'if' [ b ] x₀ 'then' { e₀ } 'else' { e₁ }" := (BranchExp b x₀ e₀ e₁)
                                                          (in custom expression_entry at level 1,
                                                              b constr at level 0,
                                                              x₀ custom var_entry at level 0,
                                                              e₀ custom expression_entry at level 0, e₁ custom expression_entry at level 0).

Notation "e₀ ; e₁" := (SeqExp e₀ e₁)
                        (in custom expression_entry at level 1,
                            e₀ custom expression_entry,
                            e₁ custom expression_entry).

Notation "{ e }" := e (in custom expression_entry at level 0, e constr at level 0).

Print Custom Grammar expression_entry.

Notation "⦃ e ⦄" := (e) (at level 0, e custom expression_entry at level 0).

Definition example_expression := ⦃ x = y ⊕ z ; if x then { ret = y ⊕ a} else { ret = z ⊕ a}⦄.
Compute example_expression.

Inductive expression_contains_branch : expression → branch → Prop :=
(* no case for op *)
| BranchCBexact : ∀ b b' x e₀ e₁ , (b = b') →
                                   expression_contains_branch ⦃if[b'] (x) then {{e₀}} else {{e₁}}⦄ b
| BranchCBleft : ∀ b b' x e₀ e₁ , (expression_contains_branch e₀ b) →
                                  expression_contains_branch ⦃if[b'] (x) then {{e₀}} else {{e₁}}⦄ b
| BranchCBright : ∀ b b' x e₀ e₁ , (expression_contains_branch e₁ b) →
                                   expression_contains_branch ⦃if[b'] (x) then {{e₀}} else {{e₁}}⦄ b
| SeqCBleft : ∀ e₀ e₁ b, (expression_contains_branch e₀ b) →
                         expression_contains_branch ⦃{e₀}; {e₁}⦄ b
| SeqCBright : ∀ e₀ e₁ b, (expression_contains_branch e₁ b) →
                          expression_contains_branch ⦃{e₀}; {e₁}⦄ b.

Inductive expression_contains_op : expression → operator → Prop :=
| OpCOExact : ∀ x₀ x₁ x₂ op, expression_contains_op ⦃(x₀) = (x₁) ⊕[op] (x₂)⦄ op
| BranchCOleft : ∀ b x e₀ e₁ op, (expression_contains_op e₀ op) →
                                 expression_contains_op ⦃if[b] (x) then {{e₀}} else {{e₁}}⦄ op
| BranchCOright : ∀ b x e₀ e₁ op, (expression_contains_op e₁ op) →
                                  expression_contains_op ⦃if[b] (x) then {{e₀}} else {{e₁}}⦄ op
| SeqCOleft : ∀ e₀ e₁ op, (expression_contains_op e₀ op) →
                          expression_contains_op ⦃{e₀}; {e₁}⦄ op
| SeqCOright : ∀ e₀ e₁ op, (expression_contains_op e₁ op) →
                           expression_contains_op ⦃{e₀}; {e₁}⦄ op.


Definition expressions_disjoint e₀ e₁ : Prop :=
  (¬ ∃ b', (expression_contains_branch e₀ b') ∧ (expression_contains_branch e₁ b')) ∧
    (¬ ∃ op, (expression_contains_op e₀ op) ∧ (expression_contains_op e₁ op)).        

Inductive expression_well_formed : expression → Prop :=
| OpWF : ∀ x₀ x₁ x₂ op, expression_well_formed ⦃(x₀) = (x₁) ⊕[op] (x₂)⦄
| BranchWF : ∀ x b e₀ e₁,
    (¬ expression_contains_branch e₀ b) →
    (¬ expression_contains_branch e₁ b) →
    (expressions_disjoint e₀ e₁) →
    
    expression_well_formed ⦃if[b] (x) then {{e₀}} else {{e₁}}⦄
| SeqWF : ∀ e₀ e₁,
    (expressions_disjoint e₀ e₁) →
    expression_well_formed ⦃{e₀}; {e₁}⦄.

Record program := 
  mkProgram {
      body : expression;
      body_wf : expression_well_formed body
    }.

Fixpoint make_wf_expression e op_num br_num :=
  (* this would be so much easier to write monadically... *)
  match e with
  | ⦃(x₀) = (x₁) ⊕[_] (x₂)⦄ =>
      (⦃(x₀) = (x₁) ⊕[Op op_num] (x₂)⦄, op_num + 1, br_num)
  | ⦃if[_] (x) then {{e₀}} else {{e₁}}⦄ =>
      match (make_wf_expression e₀ op_num (br_num + 1)) with
             (e₀', op_num₀, br_num₀) =>
               match (make_wf_expression e₁ op_num₀ br_num₀) with
                 (e₁', op_num₁, br_num₁) =>
                   (⦃if[Branch br_num] (x) then {{e₀'}} else {{e₁'}}⦄, op_num₁, br_num₁) end end
  | ⦃{e₀}; {e₁}⦄ =>
      match (make_wf_expression e₀ op_num br_num) with
        (e₀', op_num₀, br_num₀) =>
          match (make_wf_expression e₁ op_num₀ br_num₀) with
            (e₁', op_num₁, br_num₁) =>
              (⦃{e₀'}; {e₁'}⦄, op_num₁, br_num₁) end end

  end.

Definition make_wf_expression_top e :=
  match (make_wf_expression e 0 0) with
  | (e', _, _) => e'
  end.

Lemma make_wf_expression_top_sound : ∀ e, expression_well_formed (make_wf_expression_top e).
(* TODO: come back and do this soundness proof sometime
   A useful intermediary lemma would state that if
   (make_wf_expression e o br = e' o' br'), then e' uses only operator numbers
   betqeen o and o' and branch numbers between br and br'
 *)
  Admitted.

Definition make_program e : program :=
  mkProgram (make_wf_expression_top e) (make_wf_expression_top_sound e).


