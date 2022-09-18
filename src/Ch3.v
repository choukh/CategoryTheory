(*** Coq coding by choukh, Aug 2022 ***)

Require Import Lib.
From Category.Instance Require Import Poset Ens Sets Zero One.
From Category.Algebra Require Import Monoid.
From Category.Construction Require Import Opposite.

(** 3 Important Kinds Of Categories **)
Section Ch3.

(** 3.1 Preorders **)
Import Relation_Definitions RelationClasses.

(* preorder *)
Check (@Proset : ∀ A (R : relation A), PreOrder R → Category).

(* partial order *)
Check (@Poset : ∀ C (R : relation obj[C]), PreOrder R → Asymmetric R → Category).

(** 3.2 The Category Of Sets **)

(* cat of setoids *)
Check (Sets : Category).

(* cat of coq types *)
Check (Coq : Category).

(** 3.4 The Category Of Graphs **)

(* Directed multigraphs with loops *)
(* kind of like 'categories' without id and comp. *)
Record Graph := {
  vertex :> Type;
  edge : Type;
  endpoint : bool → edge → vertex;
  source := endpoint true;
  target := endpoint false
}.
Arguments source {_}.
Arguments target {_}.

Record Graph_Morph (A B : Graph) := {
  αᵥ :> A → B;
  αₑ : edge A → edge B;
  source_morph e : source (αₑ e) = αᵥ (source e);
  target_morph e : target (αₑ e) = αᵥ (target e)
}.

Global Instance Graph_Morph_Setoid {A B} : Setoid (Graph_Morph A B).
Proof. construct.
  - intros F G. exact ((∀ x, F x = G x) ∧ ∀ e, F.(αₑ) e = G.(αₑ) e).
  - firstorder congruence.
Defined.

Import Setoid Category.

Program Definition Gph : Category := {|
  obj := Graph;
  hom := Graph_Morph;
  homset := @Graph_Morph_Setoid;
  id X := {| αᵥ x := x |};
  compose X Y Z f g := {| αᵥ := Basics.compose f g |};
|}.
Next Obligation. destruct f, g; auto. Defined.
Next Obligation. destruct f, g; simpl; congruence. Defined.
Next Obligation. destruct f, g; simpl; congruence. Defined.
Next Obligation.
  proper. congruence.
  destruct x0, y0, x1, y1. simpl in *. congruence.
Defined.
Next Obligation. destruct f; auto. Defined.
Next Obligation. destruct f; auto. Defined.
Next Obligation. destruct f, g, h; auto. Defined.
Next Obligation. destruct f, g, h; auto. Defined.

(** 3.5 Monoids **)

(* empty cat *)
Check (_0 : Category).

(* one object one arrow cat *)
Check (_1 : Category).

(* one object many arrows cat *)

Variable A : Type.
Hypothesis setoid_A : Setoid A.
Hypothesis monoid_A : @Monoid A setoid_A.

Definition monoid : Category := {|
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

(** 3.6 Duality **)

Check (Opposite : Category → Category).

(* opposite involution *)
Check (@op_invol : ∀ C : Category, C^op^op = C).

End Ch3.
