(*** Coq coding by choukh, Aug 2022 ***)

Require Import Lib.
From Category.Construction Require Import Isomorphism.

(** 5.1 **)

Section Ch5_1.
Variable ℂ : Category.
Variable A B : ℂ.
Variable f : A ≅ B.

Variable j : B ~> A.
Hypothesis j_from : j ∘ f ≈ id.

Fact inverse_unique : j ≈ f⁻¹.
Proof.
  now rewrite <- id_right, <- (iso_to_from f),
    comp_assoc, j_from, id_left.
Qed.

End Ch5_1.
