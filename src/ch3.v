(*** Coq coding by choukh, Aug 2022 ***)

Set Warnings "-notation-overridden".
Set Implicit Arguments.
Set Universe Polymorphism.

Require Import Utf8_core.
From Category Require Import Lib.Setoid.
From Category.Instance Require Import Poset Ens Sets Zero One.
From Category.Algebra Require Import Monoid.
From Category.Construction Require Import Opposite.

(** 3 Important Kinds Of Categories **)
Section ch3.

(** 3.1 Preorders **)

(* preorder *)
Check Proset.

(* partial order *)
Check Poset.

(** 3.2 The Category Of Sets **)

(* cat of structural sets *)
Check Ens.

(* cat of setoids *)
Check Sets.

(* cat of coq types *)
Check Coq.

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

Definition Gph : Category.
Proof.
  unshelve eapply (Build_Category Graph Graph_Morph).
  - intros. unshelve eexists.
    + intros F G. apply (∀ x, F x = G x).
    + split; congruence.
  - intros. unshelve eexists; auto.
  - intros A B C [] []. unshelve eexists.
    + intros a. apply (αᵥ0 (αᵥ1 a)).
    + intros a b e. simpl. auto.
  - intros A B C [] [] eq1 [] [] eq2 a. simpl in *.
    rewrite eq1, eq2. reflexivity.
  - intros A B [] a; reflexivity.
  - intros A B [] a; reflexivity.
  - intros A B C D [] [] []; simpl; reflexivity.
  - intros A B C D [] [] []; simpl; reflexivity.
Defined.

(** 3.5 Monoids **)

(* empty cat *)
Check _0.

(* one object one arrow cat *)
Check _1.

(* one object many arrows cat *)

Variable A : Type.
Hypothesis setoid_A : Setoid A.
Hypothesis monoid_A : @Monoid A setoid_A.

Definition cat_of_monoid : Category := {|
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

Check Opposite.

(* opposite involution *)
Check op_invol.

End ch3.
