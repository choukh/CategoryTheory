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

Program Definition Preₛ : Subcategory Cat := {|
  sobj C := ∃ R, @RelationClasses.PreOrder C R
    ∧ (∀ x y, R x y ↔ x ~> y) (* arrow represents R *)
    ∧ (∀ x y (f g : x ~> y), f ≈ g); (* at most one arrow *)
  (* preorder homomorphism *)
  shom C D Rc Rd F := ∀ x y : C, ``Rc x y → ``Rd (F x) (F y);
|}.

Definition Pre : Category := Sub Cat Preₛ.

Program Definition Monₛ : Subcategory Cat := {|
  sobj C :=
    (* single object *)
    (∃ _ : C, ∀ x y : C, x = y) ∧
    (* homset is a monoid *)
    ∀ x : C, ∃ mon : @Monoid (x ~> x) (homset x x),
      @mempty _ (homset x x) mon ≈ id[x] ∧
      ∀ f g : x ~> x, @mappend _ (homset x x) mon f g ≈ f ∘ g;
  shom _ _ _ _ F :=
    (* monoid homomorphism *)
    (∀ x, fmap[F] id[x] ≈ id[fobj x]) ∧
    (∀ x, ∀ (f g : x ~> x), fmap[F] (f ∘ g) ≈ fmap[F] f ∘ fmap[F] g)
|}.
Next Obligation. split.
  - intros a. now rewrite e.
  - intros a F G. now rewrite e0.
Defined.

Definition Mon : Category := Sub Cat Monₛ.

Check (Subcategory.Full : ∀ C : Category, Subcategory C → Type).

Fact Preₛ_Full : Subcategory.Full Cat Preₛ.
Proof.
  intros C D [Rc Hc] [Rd Hd] F x y. simpl.
  intros Rxy. apply Hd, F, Hc, Rxy.
Qed.

Fact Monₛ_Full : Subcategory.Full Cat Monₛ.
Proof. intros C D oc od F. split; intros a. apply F. apply fmap_comp. Qed.

Check (Incl : ∀ (C : Category) (S : Subcategory C), Sub C S ⟶ C).

Section Inclusion.
Variable C : Category.
Variable S : Subcategory C.

Definition Incl := Incl C S.
Check (Incl : Sub C S ⟶ C).

Fact Incl_Faithful : Faithful Incl.
Proof. now split. Qed.

Lemma Incl_Full (sf: Subcategory.Full C S) : Functor.Full Incl.
Proof.
  unfold Subcategory.Full in sf.
  construct. exists g. apply sf.
  proper. all:reflexivity.
Qed.

(* This is the same lemma in lib *)
Check (Full_Implies_Full_Functor : ∀ (C : Category) (S : Subcategory C),
  Subcategory.Full C S → Full (Subcategory.Incl C S)).

End Inclusion.

Fact Pre_Incl_Full : Full (Incl Preₛ).
Proof. apply Incl_Full, Preₛ_Full. Qed.

Fact Mon_Incl_Full : Full (Incl Monₛ).
Proof. apply Incl_Full, Monₛ_Full. Qed.

(** 4.5 **)

Section Slice.
Variable A B C : Set.
Variable f : A → bool.
Variable g : B → bool.
Variable h : C → bool.

Let ℂ := Coq ̸ bool.
Check (obj[ℂ] = ∃ T, T → bool).

Let a : ℂ := (A; f).
Let b : ℂ := (B; g).
Let c : ℂ := (C; h).

Check ((a ~> a) = ∃ F : A → A, ∀ x : A, f x = f (F x)).
Check ((a ~> b) = ∃ F : A → B, ∀ x : A, f x = g (F x)).

Fact id_ℂ (d : ℂ) (x : ``d) : (``id[d]) x = x.
Proof. trivial. Qed.

Variable F : a ~> b.
Variable G : b ~> c.
Check (``(G ∘ F) : A → C).

End Slice.
