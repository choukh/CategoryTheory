(*** Coq coding by choukh, Aug 2022 ***)

Require Import Lib Ch3.
From Coq.Sets Require Import Powerset.
From Category.Theory Require Import Functor.
From Category.Instance Require Import Cat Coq Sets.
Local Existing Instance is_setoid.

(** 4.1 **)
Check Functor.
Check Functor.Compose.

(** 4.2 **)

(* forgetful funtor from Gph to Coq *)
Example F : Gph ⟶ Coq.
Proof.
  apply (Build_Functor Gph Coq (@vertex) (@αᵥ)).
  congruence. firstorder.
  intros A B C [] [] x; reflexivity.
Defined.

(* power funtor on Sets *)
Program Example P : Sets ⟶ Sets := {|
  fobj A := let equiv := @equiv _ (is_setoid A) in {|
    carrier := ∃ p : A → Type, ∀ x y, equiv x y → p x ↔ p y;
    is_setoid := {| equiv p q := ∀ x, ``p x ↔ ``q x |}
  |};
  fmap A B f := {|
    morphism p := existT
      (λ p : B → Type, ∀ x y : B, x ≈ y → p x ↔ p y)
      (λ b, ∃ a, ``p a ∧ f a ≈ b) _
  |}
|}.
Next Obligation. equivalence; firstorder. Defined.
Next Obligation.
  split; intros [c H]; exists c; intuition; rewrites; reflexivity.
Defined.
Next Obligation. proper; firstorder. Defined.
Next Obligation. proper; rewrites; reflexivity. Defined.
Next Obligation. split. firstorder. now exists x1. Defined.
Next Obligation.
  split; intros [b [H fb]].
  - exists (g b). split; trivial. now exists b.
  - destruct H as [c [H gc]]. exists c. split; trivial.
    rewrite <- fb. now apply f.
Defined.
