(*** Coq coding by choukh, Sep 2022 ***)

Require Ch3 Lib.
From Category.Theory Require Natural.Transformation.
From Category.Instance Require Cat Coq Fun Parallel.
Import Lib.

Section Ch6_1.
Import Natural.Transformation.
Context {C D : Category} {F G H J : C ⟶ D}.

Fact nat_id_left (N : F ⟹ G) : nat_id ∙ N ≈ N.
Proof. unfold nat_id; simpl; intros; cat. Qed.

Fact nat_id_right (N : F ⟹ G) : N ∙ nat_id ≈ N.
Proof. unfold nat_id; simpl; intros; cat. Qed.

Fact nat_comp_assoc (M : H ⟹ J) (N : G ⟹ H) (O : F ⟹ G) :
  M ∙ (N ∙ O) ≈ (M ∙ N) ∙ O.
Proof. unfold nat_compose; simpl; intros; cat. Qed.

End Ch6_1.

Section Ch6_1.
Import Fun.
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

End Ch6_1.

Section Ch6_1_1.
Import Fun.
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

End Ch6_1_1.

Section Ch6_3.
Import Ch3 Cat Coq Fun Parallel Opposite.

Program Definition Gph_Iso : [Parallel^op, Coq] ≅ Gph := {|
  to := {|
    fobj F := {|
      vertex := F ParX;
      edge := F ParY;
      endpoint b := match b with
        | true => fmap[F] (true; ParOne)
        | false => fmap[F] (false; ParTwo)
        end
    |};
    fmap _ _ f := {|
      αᵥ a := f _ a;
      αₑ e := f _ e;
      source_morph := symmetry f.(naturality_sym);
      target_morph := f.(naturality)
    |};
    fmap_id F := (λ x, F.(fmap_id) x, λ x, F.(fmap_id) x)
  |};
  from := {|
    fobj G := {|
      fobj x := match x with 
        | ParX => G.(vertex)
        | ParY => G.(edge)
        end;
      fmap x y f := match x, y with
        | ParX, ParX => id
        | ParY, ParY => id
        | ParX, ParY => False_rect _ (ParHom_Y_X_absurd _ (`2 f))
        | ParY, ParX => match ``f with
          | true  => G.(source)
          | false => G.(target)
          end
        end
    |};
    fmap _ _ f := {|
      transform x := match x with
        | ParX => f.(αᵥ)
        | ParY => f.(αₑ)
        end
    |}
  |};
  iso_to_from := (λ A, {|
    to := {| αᵥ := λ x, x; αₑ := λ x, x |};
    from := {| αᵥ := λ x, x; αₑ := λ x, x |}
  |}; _);
  (* iso_from_to := (λ F, {|
    to := _
  |}; _) *)
|}.
(* from.fobj.fmap_respects *)
Next Obligation. proper. now destruct e0; destruct e. Defined.
(* from.fobj.fmap_id *)
Next Obligation. destruct x; reflexivity. Defined.
(* from.fobj.fmap_comp *)
Next Obligation. destruct X; dependent destruction X0; reflexivity. Defined.
(* from.fmap.naturality *)
Next Obligation. destruct X; destruct f; simpl; congruence. Defined.
(* from.fmap.naturality_sym *)
Next Obligation. destruct X; destruct f; simpl; congruence. Defined.
(* from.fmap_respects *)
Next Obligation. proper. destruct A; trivial. Defined.
(* from.fmap_id *)
Next Obligation. destruct A; reflexivity. Defined.
(* from.fmap_comp *)
Next Obligation. destruct A; destruct f, g; reflexivity. Defined.
(* iso_to_from.functor_equiv.iso.condition *)
Next Obligation. destruct f; easy. Defined.
(* iso_from_to.functor_equiv *)
Next Obligation. unshelve eexists.
  - (* iso *) intros F. construct.
    + (* to *) transform; simpl.
      * intros []; trivial.
      * (* natuality *)
        destruct F; destruct f; dependent destruction p; simpl.
        1-2:rewrite fmap_id. all:reflexivity.
      * (* natuality_sym *)
        destruct F; destruct f; dependent destruction p; simpl.
        1-2:rewrite fmap_id. all:reflexivity.
    + (* from *) transform; simpl.
      * intros []; trivial.
      * (* natuality *)
        destruct F; destruct f; dependent destruction p; simpl.
        1-2:rewrite fmap_id. all:reflexivity.
      * (* natuality_sym *)
        destruct F; destruct f; dependent destruction p; simpl.
        1-2:rewrite fmap_id. all:reflexivity.
    + (* iso_to_from *)
      destruct F; destruct A; simpl; rewrite fmap_id; reflexivity.
    + (* iso_from_to *) destruct A; reflexivity.
  - intros F G n []; reflexivity.
Defined.

End Ch6_3.
