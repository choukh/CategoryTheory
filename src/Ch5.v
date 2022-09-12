(*** Coq coding by choukh, Aug 2022 ***)

Require Ch3 Lib.
From Category.Theory Require Morphisms.
From Category.Construction Require Isomorphism Slice.
From Category.Instance Require Coq.
From Category.Structure Require Terminal.
Import Lib.

(** 5.1 **)
Section Ch5_1.
Import Isomorphism.
Context {ℂ : Category} {A B : ℂ}.

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
Context {ℂ : Category}.

Variable T T' : @Terminal ℂ.
Local Definition t := @terminal_obj ℂ T.
Local Definition t' := @terminal_obj ℂ T'.

Fact terminal_unique : t ≅ t'.
Proof.
  construct. apply one. apply one.
  rewrite one_unique. reflexivity.
  rewrite one_unique. reflexivity.
Qed.

Program Definition another_terminal (a : ℂ) (iso : a ≅ 1) := {|
  terminal_obj := a;
  one x := iso⁻¹ ∘ one[x]
|}.
Next Obligation.
  destruct iso.
  rewrite <- id_left, <- (id_left g).
  rewrite <- iso_from_to, !comp_assoc_sym.
  f_equiv. apply one_unique.
Defined.

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
Context {B C : Coq} {f : B ~> C}.

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
  - intros H. split. intros D g h eq y.
    destruct (H y) as [x <-]. apply eq.
  - intros [epic] y.
    specialize epic with Prop (λ y, (exists x, f x = y)%type) (λ _, True).
    simpl in epic. erewrite epic. trivial. intros x.
    apply PE. firstorder eauto.
Qed.

End Ch5_4.

(** 5.6 **)
Section Ch5_6.
Import Morphisms.
Context {ℂ : Category} {B C : ℂ} {f : B ~> C}.

Fact splitEpi_epic : SplitEpi f → Epic f.
Proof.
  intros [s Hs]. constructor. intros A g1 g2 eq.
  rewrite <- (id_right g1), <- (id_right g2), <- Hs, !comp_assoc.
  now rewrite eq.
Qed.

Fact splitMono_monic : SplitMono f → Monic f.
Proof.
  intros [r Hr]. constructor. intros A g1 g2 eq.
  rewrite <- (id_left g1), <- (id_left g2), <- Hr, !comp_assoc_sym.
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

Corollary iso_epic (iso : B ≅ C) : Epic iso.
Proof. apply splitEpi_epic, iso_splitEpi. Qed.

Corollary iso_monic (iso : B ≅ C) : Monic iso.
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

Section Ch5_7.
Import Morphisms Terminal.
Context {ℂ : Category} `{@Terminal ℂ} {B : ℂ}.

Fact monic_point (p : 1 ~> B) : Monic p.
Proof. construct. apply one_unique. Qed.

End Ch5_7.

Section Ch5_8.
Import Ch3 Terminal.

Program Instance terminal_of_Gph : @Terminal Gph := {|
  terminal_obj := {|
    vertex := unit;
    edge _ _ := unit
  |}
|}.
Next Obligation. construct; apply tt. Defined.
Next Obligation. destruct f, g. simpl. now rewrite αᵥ, αᵥ0. Defined.

Import Slice.
Context {ℂ : Category}.

Program Instance terminal_of_slice (X : ℂ) : @Terminal (ℂ ̸ X) := {|
  terminal_obj := (X; id[X]);
|}.
Next Obligation. rewrite id_left in X0, X1. now rewrites. Defined.

Fact point_in_slice (X : ℂ) (b : ℂ ̸ X) (s : 1 ~> b) : `2 b ∘ `1 s ≈ id[X].
Proof. destruct b as [B b], s as [s bs]. simpl in *. apply bs. Qed.

End Ch5_8.
