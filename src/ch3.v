(*** Coq coding by choukh, Aug 2022 ***)

Set Warnings "-notation-overridden".
Set Implicit Arguments.
Set Universe Polymorphism.

Require Import Utf8_core.
From Category Require Import Lib.
From Category.Instance Require Import Proset Poset Ens Sets Zero One.
From Category.Algebra Require Import Monoid.
From Category.Construction Require Import Opposite.

Section ch3.

(* 3.1 *)
Check Proset.
Check Poset.

(* 3.2 *)
Check Ens.
Check Sets.

(* 3.4 *)
(* I can't a definition of directed graph in the category library *)

Record graph := {
  vertex : Type;
  edge := prod vertex vertex;
  source (e : edge) := fst e;
  target (e : edge) := snd e
}.

Record graph_morph (X Y : graph) := {
  αᵥ : vertex X → vertex Y;
  αₑ : edge X → edge Y;
  source_morph (e : edge X) : αᵥ (source e) = source (αₑ e);
  target_morph (e : edge X) : αᵥ (target e) = target (αₑ e)
}.

Definition Gph : Category.
Proof.
  unshelve eapply (Build_Category graph graph_morph).
  - intros. unshelve eexists. intros F G. apply True. auto.
  - intros. unshelve eexists; trivial.
  - intros x y z [] []. unshelve eexists.
    intros a. apply (αᵥ0 (αᵥ1 a)).
    intros a. apply (αₑ0 (αₑ1 a)). all:congruence.
  - firstorder.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(* 3.5 *)

(* empty cat *)
Check _0.

(* one obj cat *)
Check _1.

Variable A : Type.
Hypothesis setoid_A : Setoid A.
Hypothesis monoid_A : @Monoid A setoid_A.

Definition cat_of_monoid : Category :=
  {|
    obj := unit;
    hom _ _ := A;
    homset _ _ := setoid_A;
    id _ := mempty;
    compose _ _ _ := mappend;
    compose_respects _ _ _ := mappend_respects;
    id_left _ _ := mempty_left;
    id_right _ _ := mempty_right;
    comp_assoc _ _ _ _ f g h := symmetry (mon_assoc f g h);
    comp_assoc_sym _ _ _ _ := mon_assoc;
  |}.

(* 3.5 *)
Check Opposite.
Check op_invol.

End ch3.
