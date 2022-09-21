(*** Coq coding by choukh, Sep 2022 ***)

Require Import Lib.
From Category.Theory Require Import Sheaf.
From Category.Instance Require Import Fun Sets.
From Category.Construction Require Import Opposite.

Program Definition Hom {C : Category} (a : C) : C ⟶ Sets := {|
  fobj x := {|
    carrier := a ~> x : Type;
    is_setoid := homset a x : Setoid (a ~> x)
  |} : SetoidObject;
  fmap x y (f : x ~> y) := {|
    morphism (g : a ~> x) := f ∘ g : a ~> y
  |} : SetoidMorphism _ _
|}.
Notation "Hom( a , -)" := (Hom a) (format "Hom( a ,  -)").

Program Definition CoHom {C : Category} (a : C) : C^op ⟶ Sets := {|
  fobj x := {|
    carrier := a ~{C^op}~> x : Type;
    is_setoid := @homset (C^op) a x : Setoid (a ~{C^op}~> x)
  |} : SetoidObject;
  fmap x y (f : x ~{C^op}~> y) := {|
    morphism (g : a ~{C^op}~> x) := f ∘ g : a ~{C^op}~> y
  |} : SetoidMorphism _ _
|}.
Notation "Hom(-, a )" := (CoHom a) (format "Hom(-,  a )").

Print Hom.

Program Definition Curried_Hom {C : Category} : C^op ⟶ [C, Sets] := {|
  fobj (a : C) := Hom(a, -) : C ⟶ Sets;
  fmap (x y : C) (f : y ~{C}~> x):= {|
    transform z := {|
      morphism (g : x ~{C}~> z) := g ∘ f : y ~{C}~> z;
    |} : SetoidMorphism (homset x z) (homset y z)
  |} : Hom(x, -) ⟹ Hom(y, -)
|}.

Program Definition Curried_CoHom {C : Category} : C ⟶ [C^op, Sets] := {|
  fobj (a : C) := Hom(-, a) : C^op ⟶ Sets;
  fmap (x y : C) (f : y ~{C^op}~> x):= {|
    transform z := {|
      morphism (g : x ~{C^op}~> z) := g ∘ f : y ~{C^op}~> z;
    |} : SetoidMorphism (@homset C^op x z) (@homset C^op y z)
  |} : Hom(-, x) ⟹ Hom(-, y)
|}.

Coercion Curried_Hom : Category >-> Functor.

Section CoYoneda.
Context {C : Category} (a : C) (F : C ⟶ Sets).

Global Program Instance Co_Yoneda_Lemma : Copresheaves Hom(a, -) F ≅ F a := {|
  to := {|
    morphism (η : Hom(a, -) ⟹ F) := η a id : F a;
    proper_morphism := _ (* auto *)
  |} : SetoidMorphism nat_Setoid (F a);
  from := {|
    morphism (s : F a) := {|
      transform (x : C) := {|
        morphism (f : a ~> x) := fmap[F] f s : F x;

        proper_morphism (f g : a ~> x) (eq : f ≈ g) :=
          (* (1) *) _ : fmap[F] f s ≈ fmap[F] g s

      |} : SetoidMorphism (homset a x) (F x);

      naturality (x y : C) (f : x ~> y) (g : a ~> x) :=
        (* (2) *) _ : fmap[F] f (fmap[F] g s) ≈ fmap[F] (f ∘ g) s;

      naturality_sym (x y : C) (f : x ~> y) (g : a ~> x) :=
        (* (3) *) _ : fmap[F] (f ∘ g) s ≈ fmap[F] f (fmap[F] g s)

    |} : Hom(a, -) ⟹ F;

    proper_morphism (s t : F a) (eq: s ≈ t) (x : C) (f : a ~> x) :=
      (* (4) *) _ : fmap[F] f s ≈ fmap[F] f t
  |} : SetoidMorphism (F a) nat_Setoid;
  iso_to_from (s : F a) :=
    (* (5) *) _ : fmap[F] id s ≈ s;

  iso_from_to (η : Hom(a, -) ⟹ F) (x : C) (f : a ~> x) :=
    (* (6) *) _ : fmap[F] f (η a id) ≈ η x f
|}.
(* (1): [transform] preserves morphism equivalences *)
Next Obligation. destruct F; simpl in *. apply fmap_respects, eq. Defined.
(* (2): The action of [transform] is natural *)
Next Obligation. destruct F; simpl in *. symmetry. apply fmap_comp. Defined.
(* (3): The action of [transform] is natural (symmetric) *)
Next Obligation. destruct F; simpl in *. apply fmap_comp. Defined.
(* (4): [from] preserves morphism equivalences *)
Next Obligation. apply proper_morphism; assumption. Defined.
(* (5): The result of [from] respects the laws of the functor category *)
Next Obligation. destruct F; simpl in *. apply fmap_id. Defined.
(* (6): The result of [from] preserves morphism equivalences *)
Next Obligation. destruct F, η; simpl in *. rewrite naturality. apply transform; cat. Defined.

End CoYoneda.

Section Yoneda.
Context {C : Category} (a : C) (F : C^op ⟶ Sets).

Global Program Instance Yoneda_Lemma : Presheaves Hom(-, a) F ≅ F a := {|
  to := {| morphism η := η a id; |};
  from := {| morphism s := {|
    transform x := {| morphism f := fmap[F] f s : F x |};
  |}|};
|}.
Next Obligation. proper. destruct F; simpl in *. apply fmap_respects, X. Defined.
Next Obligation. destruct F; simpl in *. symmetry. apply fmap_comp. Defined.
Next Obligation. destruct F; simpl in *. apply fmap_comp. Defined.
Next Obligation. proper. apply proper_morphism; assumption. Defined.
Next Obligation. destruct F; simpl in *. apply fmap_id. Defined.
Next Obligation. destruct F, x; simpl in *. rewrite naturality. apply transform; cat. Defined.

End Yoneda.

Section YonedaEmbedding.
Context {C : Category} (A B : C).

Global Instance よ : Presheaves Hom(-, A) Hom(-, B) ≊ A ~> B.
Proof. apply Yoneda_Lemma. Defined.

Global Instance Coよ : Copresheaves Hom(A, -) Hom(B, -) ≊ B ~> A.
Proof. apply Co_Yoneda_Lemma. Defined.

End YonedaEmbedding.
