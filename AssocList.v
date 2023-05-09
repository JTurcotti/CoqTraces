(*
This file contains useful utilities for dealing with association lists
 *)

From Coq Require Import Lists.List Unicode.Utf8.
Import ListNotations.

Module Type WithEq.
  Parameter t : Type.
  Parameter eq : t → t → Prop.
  Parameter eq_dec : ∀ (x x' : t), {eq x x'} + {¬ eq x x'}.
End WithEq.

Module AssocList (A B : WithEq).

  Definition assoc_list := list (A.t * B.t).

  Definition t := assoc_list.

  Fixpoint lookup (l : assoc_list) (a : A.t) : option B.t :=
    match l with
    | [] => None
    | (a', b') :: l_tail =>
        if (A.eq_dec a a') then Some b' else
          lookup l_tail a
    end.

    
  Definition contains (l : assoc_list) a b : Prop :=
    lookup l a = Some b.
  
  Definition eq l₁ l₂ : Prop :=
    ∀ a b, contains l₁ a b ↔ contains l₂ a b.

  Global Notation "[ l ; a ↦ b ]" := ((a, b) :: l).
End AssocList.
