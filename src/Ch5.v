(*** Coq coding by choukh, Aug 2022 ***)

Require Import Lib.
From Category.Theory Require Morphisms.
From Category.Construction Require Isomorphism Slice.
From Category.Instance Require Coq.
From Category.Structure Require Terminal.

(** 5.1 **)
Section Ch5_1.
Import Isomorphism.

Variable ℂ : Category.
Variable A B : ℂ.
Variable f : A ≅ B.

Variable j : B ~> A.
Hypothesis j_from : j ∘ f ≈ id.

Fact inverse_unique : j ≈ f⁻¹.
Proof.
  now rewrite <- id_right, <- (iso_to_from f),
    comp_assoc, j_from, id_left.
Qed.

End Ch5_1.

(** 5.2 **)
Section Ch5_2.
Import Isomorphism Terminal.

Variable C : Category.
Variable T T' : @Terminal C.
Local Definition t := @terminal_obj C T.
Local Definition t' := @terminal_obj C T'.

Fact terminal_unique : t ≅ t'.
Proof.
  construct. apply one. apply one.
  rewrite one_unique. reflexivity.
  rewrite one_unique. reflexivity.
Qed.

Program Definition another_terminal (a : C) (iso : a ≅ 1) := {|
  terminal_obj := a;
  one x := iso⁻¹ ∘ one[x]
|}.
Next Obligation.
  destruct iso.
  rewrite <- id_left, <- (id_left g).
  rewrite <- iso_from_to, !comp_assoc_sym.
  f_equiv. apply one_unique.
Defined.

Import Slice.
Program Example terminal_of_slice (a : C) : @Terminal (C ̸ a) := {|
  terminal_obj := (a; id[a]);
|}.
Next Obligation. rewrite id_left in X0, X. now rewrites. Defined.

End Ch5_2.

(** 5.3 **)
Section Ch5_3.
Import Coq.

Fact coq_well_pointed (B C : Coq) (f g : B ~> C) :
  f ≈ g ↔ ∀ b : 1 ~> B, f ∘ b ≈ g ∘ b.
Proof. split.
  - intros eq A. now rewrites.
  - intros H x. specialize H with (λ _, x). simpl in H. tauto.
Qed.

Fact arrow_extensionality {ℂ : Category} (B C : ℂ) (f g : B ~> C) :
  f ≈ g ↔ ∀ A (x: A ~> B), f ∘ x ≈ g ∘ x.
Proof. split.
  - intros eq A x. now rewrites.
  - intros H. specialize H with B id. now rewrite !id_right in H.
Qed.

End Ch5_3.

(** 5.4 **)
Section Ch5_4.
Import Morphisms Coq.

Fact injectivity_is_monic {B C : Coq} (f : B ~> C) :
  (∀ x y, f x = f y → x = y) ↔ Monic f.
Proof. split.
  - intros inj. construct. apply inj, H.
  - intros [monic] x y eq.
    specialize monic with 1 (λ _, x) (λ _, y).
    simpl in monic. tauto.
Qed.

Fact surjectivity_is_epic {B C : Coq} (f : B ~> C) :
  (forall y, exists x, f x = y) ↔ Epic f.
Proof. split.
  - intros H. split. intros D g h eq.
    intros y. destruct (H y) as [x <-]. apply eq.
  - intros [epic] y.
    specialize epic with Prop (λ y, (exists x, f x = y)%type) (λ _, True).
    erewrite epic; trivial. simpl. intros x.
    Axiom PE : ∀ P Q, (P <-> Q -> P = Q).
    apply PE. firstorder eauto.
Qed.

End Ch5_4.
