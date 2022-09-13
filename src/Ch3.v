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

(* Graphs are just like 'categories' without id and comp. *)
Class Graph := {
  vertex : Type;
  edge : crelation vertex;
  edge_setoid a b : Setoid (edge a b);
  source {a b} (e : edge a b) := a;
  target {a b} (e : edge a b) := b
}.
Coercion vertex : Graph >-> Sortclass.
Existing Instance edge_setoid.

Class Graph_Morph (A B : Graph) := {
  αᵥ : A → B;
  αₑ {a b : A} : edge a b → edge (αᵥ a) (αᵥ b);
}.
Coercion αᵥ : Graph_Morph >-> Funclass.

Fact source_morph {A B} {_ : Graph_Morph A B} {a b : A} :
  ∀ e : edge a b, αᵥ (source e) = source (αₑ e).
Proof. trivial. Qed.

Fact target_morph {A B} {_ : Graph_Morph A B} {a b : A} :
  ∀ e : edge a b, αᵥ (target e) = target (αₑ e).
Proof. trivial. Qed.

Import Setoid Category.

Program Definition Gph : Category := {|
  obj := Graph;
  hom := Graph_Morph;
  homset X Y := {| equiv F G := ∀ x, F x = G x |};
  id X := {| αᵥ x := x |};
  compose X Y Z f g := {| αᵥ := Basics.compose f g |};
|}.
Next Obligation. split; congruence. Qed.
Next Obligation. destruct f, g; simpl; auto. Qed.
Next Obligation. proper; congruence. Qed.

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
