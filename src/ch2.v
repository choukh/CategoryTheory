(*** Coq coding by choukh, Aug 2022 ***)

Set Warnings "-notation-overridden".
Set Implicit Arguments.
Set Universe Polymorphism.

Require Import Utf8_core.
From Category Require Import Lib Theory.

(** 2 Definition Of A Category **)
Section ch2.

Variable ℂ : Category.
Variable A B C : obj[ℂ].
Variable f : A ~> B.
Variable g : B ~> C.

(** 2.1 Composition **)

Fact comp : A ~> C.
Proof. apply (g ∘ f). Qed.

(** 2.2 Identity Arrows **)

Fact id_arrow : B ~> B.
Proof. apply id. Qed.

Fact id_left : id ∘ f ≈ f.
Proof. apply id_left. Qed.

Fact id_right : f ∘ id ≈ f.
Proof. apply id_right. Qed.

(** 2.3 Associativity **)

Variable D : obj[ℂ].
Variable h : C ~> C.

Fact comp_assoc : h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f.
Proof. apply comp_assoc. Qed.

Fact comp_assoc_sym : (h ∘ g) ∘ f ≈ h ∘ (g ∘ f).
Proof. apply comp_assoc_sym. Qed.

End ch2.

(** 2.4 Example **)
Section ch2_4.

Inductive object := A | B | C.
Inductive arrow : object → object → Type :=
  | id_A : arrow A A
  | id_B : arrow B B
  | id_C : arrow C C
  | f : arrow A B
  | g : arrow B C
  | h : arrow A C
  | i : arrow A C.

Example ℂ : Category.
Proof.
  unshelve eapply (Build_Category object arrow).
  - intros. unshelve eexists. intros F G. apply True. auto.
  - intros []; constructor.
  - intros [] [] [] F G; try constructor; try inversion F; inversion G.
  - auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

End ch2_4.

(** 2.5 Unique Identity Arrows **)
Section ch2_5.

Variable ℂ : Category.
Variable B : obj[ℂ].
Variable j : B ~> B.
Hypothesis j_id_left : ∀ (X : obj[ℂ]) (f : X ~> B), j ∘ f ≈ f.

Fact id_unique : j ≈ @id ℂ B.
Proof.
  pose proof (H := j_id_left B (@id ℂ B)).
  rewrite id_right in H. apply H.
Qed.

End ch2_5.
