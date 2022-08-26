(*** Coq coding by choukh, Aug 2022 ***)

Require Import Lib Ch3.
From Coq.Sets Require Import Powerset.
From Category.Algebra Require Import Monoid.
From Category.Theory Require Import Functor.
From Category.Instance Require Import Cat Coq Sets Proset.
From Category.Construction Require Import Subcategory Slice.
Local Existing Instance is_setoid.

(** 4.1 **)
Check (@Functor : Category → Category → Type).
Check (@Id : ∀ C : Category, C ⟶ C).
Check (@Compose : ∀ C D E : Category, D ⟶ E → C ⟶ D → C ⟶ E).

Check (Cat : obj[Cat]).
Check (Cat : Cat).

Fact Functor_eta : Functor = @Functor Cat Cat.
Proof. reflexivity. Qed.

(** 4.2 **)

(* forgetful funtor from Gph to Coq *)
Program Example F : Gph ⟶ Coq := {|
  fobj := @vertex;
  fmap := @αᵥ;
|}.

(* power funtor on Sets *)
Program Example P : Sets ⟶ Sets := {|
  fobj A := {|
    carrier := { p : A → Type & ∀ x y, x ≈ y → p x ↔ p y };
    is_setoid := {| equiv p q := ∀ x, ``p x ↔ ``q x |}
  |};
  fmap A B f := {|
    morphism p := existT _ (λ b, ∃ a, ``p a ∧ f a ≈ b) _
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

(** 4.3 **)
Check (@Full: ∀ C D : Category, C ⟶ D → Type).
Check (@Faithful : ∀ C D : Category, C ⟶ D → Type).

(** 4.4 **)

Check (Subcategory : Category → Type).
Check (Subcategory.Sub : ∀ C : Category, Subcategory C → Category).
Check (Subcategory.Full : ∀ C : Category, Subcategory C → Type).

Program Definition Preₛ : Subcategory Cat := {|
  sobj C := ∃ R, @RelationClasses.PreOrder C R
    ∧ (∀ x y, R x y ↔ x ~> y)
    ∧ (∀ x y (f g : x ~> y), f ≈ g); (* at most one arrow *)
  shom C D Rc Rd F := ∀ x y : C, ``Rc x y → ``Rd (F x) (F y);
|}.

Fact Preₛ_Full : Subcategory.Full Cat Preₛ.
Proof.
  intros C D [Rc Hc] [Rd Hd] F x y. simpl.
  intros Rxy. apply Hd, F, Hc, Rxy.
Qed.

Definition Pre : Category := Sub Cat Preₛ.

Program Definition Monₛ : Subcategory Cat := {|
  sobj C := ∃ x : C, ∀ x y : C, x = y (* single object *)
    ∧ @Monoid (x ~> y) (homset x y); (* homset is a monoid *)
  (* monoid homomorphism *)
  shom C D oc od F := (∀ x, fmap[F] id[x] ≈ id[fobj x])
    ∧ ∀ x y (f g : x ~> y), fmap[F] (f ∘ g) ≈ fmap[F] f ∘ fmap[F] g
|}.
Next Obligation. firstorder. Defined.
Next Obligation. firstorder. Defined.
Next Obligation. split.
  - intros a. now rewrite e.
  - intros a b F G. now rewrite e0.
Defined.

Fact Monₛ_Full : Subcategory.Full Cat Monₛ.
Proof.
  intros C D [] [] F. split.
  - intros a. apply F.
  - intros a b f g. rewrite fmap_comp. f_equiv.
    pose proof (p a b) as [eq []]. subst. simpl.
    
Admitted.

Definition Mon : Category := Sub Cat Monₛ.
