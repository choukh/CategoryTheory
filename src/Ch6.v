(*** Coq coding by choukh, Sep 2022 ***)

Require Import Lib.
From Category.Theory Require Import Natural.Transformation.
From Category.Instance Require Import Fun.

Section Ch6.
Context {A B C D : Category} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B).

Program Definition funtor_id_left : Id ◯ F ≈ F := _.
Program Definition funtor_id_left_sym : F ≈ Id ◯ F := _.
Program Definition funtor_id_right : F ◯ Id ≈ F := _.
Program Definition funtor_id_right_sym : F ≈ F ◯ Id := _.
Program Definition funtor_comp_assoc : F ◯ (G ◯ H) ≈ (F ◯ G) ◯ H := _.
Program Definition funtor_comp_assoc_sym : (F ◯ G) ◯ H ≈ F ◯ (G ◯ H) := _.

Program Definition fun_id_left : Id ◯ F ⟹ F := {| transform := _ |}.
Program Definition fun_id_left_sym : F ⟹ Id ◯ F := {| transform := _ |}.
Program Definition fun_id_right : F ◯ Id ⟹ F := {| transform := _ |}.
Program Definition fun_id_right_sym : F ⟹ F ◯ Id := {| transform := _ |}.
Program Definition fun_comp_assoc : F ◯ (G ◯ H) ⟹ (F ◯ G) ◯ H := {| transform := _ |}.
Program Definition fun_comp_assoc_sym : (F ◯ G) ◯ H ⟹ F ◯ (G ◯ H) := {| transform := _ |}.

Program Definition nat_λ : F ◯ Id ≅[Fun] F := {|
  to := fun_id_right;
  from := fun_id_right_sym
|}.

Program Definition nat_ρ : Id ◯ F ≅[Fun] F := {|
  to := fun_id_left;
  from := fun_id_left_sym
|}.

Program Definition nat_α : F ◯ (G ◯ H) ≅[Fun] (F ◯ G) ◯ H := {|
  to := fun_comp_assoc;
  from := fun_comp_assoc_sym
|}.

End Ch6.

Section Ch6_1.
Context {C D : Category} (F G : C ⟶ D).

(* same as Functor_Setoid_Nat_Iso in lib *)
Theorem natural_iso : F ≅[Fun] G ↔ F ≈ G.
Proof. split.
  - intros []. construct.
    + isomorphism; simpl in *.
      * apply to.
      * apply from.
      * simpl. srewrite iso_to_from. cat.
      * simpl. srewrite iso_from_to. cat.
    + simpl. rewrite <- comp_assoc, (naturality[to]), comp_assoc.
      srewrite iso_from_to. cat.
  - intros [iso eq]. isomorphism; simpl.
    + transform.
      * apply iso.
      * simpl. rewrite eq, !comp_assoc, iso_to_from. cat.
      * simpl. rewrite eq, !comp_assoc, iso_to_from. cat.
    + transform.
      * apply iso.
      * simpl. rewrite eq, <- !comp_assoc, iso_to_from. cat.
      * simpl. rewrite eq, <- !comp_assoc, iso_to_from. cat.
    + simpl. rewrite iso_to_from. cat.
    + simpl. rewrite iso_from_to. cat.
Defined.

End Ch6_1.
