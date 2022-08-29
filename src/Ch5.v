(*** Coq coding by choukh, Aug 2022 ***)

Require Import Lib.
From Category.Construction Require Isomorphism.
From Category.Structure Require Terminal.

(** 5.1 **)
Section Ch5_1.
Import Isomorphism.

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

(** 5.2 **)
Section Ch5_2.
Import Isomorphism Terminal.

Variable C : Category.
Variable T T' : @Terminal C.
Local Definition t := @terminal_obj C T.
Local Definition t' := @terminal_obj C T'.

Fact terminal_unique : t ≅ t'.
Proof.
  construct. apply one. apply one.
  rewrite one_unique. reflexivity.
  rewrite one_unique. reflexivity.
Qed.

Program Definition another_terminal (a : C) (iso : a ≅ 1) := {|
  terminal_obj := a;
  one x := iso⁻¹ ∘ one[x]
|}.
Next Obligation.
  destruct iso.
  rewrite <- id_left, <- (id_left g).
  rewrite <- iso_from_to, !comp_assoc_sym.
  f_equiv. apply one_unique.
Defined.

End Ch5_2.
