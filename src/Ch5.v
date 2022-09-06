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

Context {B C : Coq}.
Variable f : B ~> C.

Fact coq_inj_iff_monic : (∀ x y, f x = f y → x = y) ↔ Monic f.
Proof. split.
  - intros inj. construct. apply inj, H.
  - intros [monic] x y eq.
    specialize monic with 1 (λ _, x) (λ _, y).
    simpl in monic. tauto.
Qed.

(** 5.5 **)

(* Propositional Extensionality *)
Hypothesis PE : ∀ P Q, (P <-> Q -> P = Q).

Fact coq_sur_iff_epic : (forall y, exists x, f x = y) ↔ Epic f.
Proof. split.
  - intros H. split. intros D g h eq.
    intros y. destruct (H y) as [x <-]. apply eq.
  - intros [epic] y.
    specialize epic with Prop (λ y, (exists x, f x = y)%type) (λ _, True).
    erewrite epic; trivial. simpl. intros x.
    apply PE. firstorder eauto.
Qed.

End Ch5_4.

(** 5.6 **)
Section Ch5_6.
Import Morphisms.

Context {ℂ : Category} {B C : ℂ}.
Variable f : B ~> C.

Fact splitMono_monic : SplitMono f → Monic f.
Proof.
  intros [s Hs]. constructor. intros A g1 g2 eq.
  rewrite <- (id_left g1), <- (id_left g2), <- Hs, !comp_assoc_sym.
  now rewrite eq.
Qed.

Fact splitEpi_epic : SplitEpi f → Epic f.
Proof.
  intros [s Hs]. constructor. intros A g1 g2 eq.
  rewrite <- (id_right g1), <- (id_right g2), <- Hs, !comp_assoc.
  now rewrite eq.
Qed.

Fact splitEpi_iff : SplitEpi f ↔ ∀ A (y : A ~> C), ∃ x : A ~> B, f ∘ x ≈ y.
Proof. split.
  - intros [s Hs] A y. exists (s ∘ y).
    now rewrite comp_assoc, Hs, id_left.
  - intros H. specialize H with C (id[C]) as [x Hx].
    econstructor. apply Hx.
Qed.

Fact splitMono_iff : SplitMono f ↔ ∀ A (y : B ~> A), ∃ x : C ~> A, x ∘ f ≈ y.
Proof. split.
  - intros [r Hr] A y. exists (y ∘ r).
    now rewrite comp_assoc_sym, Hr, id_right.
  - intros H. specialize H with B (id[B]) as [x Hx].
    econstructor. apply Hx.
Qed.

End Ch5_6.

Section Ch5_6_2.
Import Morphisms Isomorphism.

Context {ℂ : Category} {B C : ℂ}.

Fact iso_splitEpi (iso : B ≅ C) : SplitEpi iso.
Proof.
  apply splitEpi_iff. intros A y. exists (iso⁻¹ ∘ y).
  rewrite comp_assoc, iso_to_from. cat.
Qed.

Fact iso_splitMono (iso : B ≅ C) : SplitMono iso.
Proof.
  apply splitMono_iff. intros A y. exists (y ∘ iso⁻¹).
  rewrite comp_assoc_sym, iso_from_to. cat.
Qed.

Fact iso_epic (iso : B ≅ C) : Epic iso.
Proof. apply splitEpi_epic, iso_splitEpi. Qed.

Fact iso_monic (iso : B ≅ C) : Monic iso.
Proof. apply splitMono_monic, iso_splitMono. Qed.

Variable f : B ~> C.

Program Definition monic_splitEpi_forms_iso
  (m : Monic f) (e : SplitEpi f) : B ≅ C :=
{|
  to := f;
  from := e.(retract)
|}.
Next Obligation. apply e. Defined.
Next Obligation.
  destruct e as [s Hs]; simpl. apply m.
  rewrite comp_assoc, Hs. cat.
Defined.

Program Definition epic_splitMono_forms_iso
  (e : Epic f) (m : SplitMono f) : B ≅ C :=
{|
  to := f;
  from := m.(section)
|}.
Next Obligation.
  destruct m as [r Hr]; simpl. apply e.
  rewrite comp_assoc_sym, Hr. cat.
Defined.
Next Obligation. apply m. Defined.

End Ch5_6_2.
