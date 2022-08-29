(*** Coq coding by choukh, Aug 2022 ***)

Require Import Lib.
From Category Require Import Theory.

(** 2 Definition Of A Category **)
Section Ch2.

Variable ℂ : Category.
Variable A B C : ℂ.
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

Variable D : ℂ.
Variable h : C ~> D.

Fact comp_assoc : h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f.
Proof. apply comp_assoc. Qed.

Fact comp_assoc_sym : (h ∘ g) ∘ f ≈ h ∘ (g ∘ f).
Proof. apply comp_assoc_sym. Qed.

End Ch2.

(** 2.4 Example **)
Section Ch2_4.

Inductive object := A | B | C.
Inductive arrow : object → object → Type :=
  | id_A : arrow A A
  | id_B : arrow B B
  | id_C : arrow C C
  | f : arrow A B
  | g : arrow B C
  | h : arrow A C
  | i : arrow A C.

Program Example ℂ : Category := {|
  obj := object;
  hom := arrow;
  homset _ _ := {| equiv _ _ := True |}
|}.
Next Obligation.
  destruct x; constructor.
Defined.
Next Obligation.
  destruct x, y, z; try constructor; try inversion f0; inversion g0.
Defined.

End Ch2_4.

(** 2.5 Unique Identity Arrows **)
Section Ch2_5.

Variable ℂ : Category.
Variable B : ℂ.
Variable j : B ~> B.
Hypothesis j_id_left : ∀ X (f : X ~> B), j ∘ f ≈ f.

Fact id_unique : j ≈ id[B].
Proof.
  pose proof (H := j_id_left B id[B]).
  rewrite id_right in H. apply H.
Qed.

End Ch2_5.
