(*** Coq coding by choukh, Sep 2022 ***)

Require Import Lib.
From Category.Instance Require Import Cat Fun.

Global Instance functor_respects_iso :
  Proper (Isomorphism ==> Isomorphism ==> iffT) (@Functor).
Proof.
  intros A B AB C D CD. split; intros F.
  - refine {|
      fobj x := CD.(to) (F (AB⁻¹ x));
      fmap _ _ f := fmap[CD.(to)] (fmap[F] (fmap[AB⁻¹] f));
    |}.
    + proper; now rewrite X.
    + intros; now rewrite !fmap_id.
    + intros; now rewrite !fmap_comp.
  - refine {|
      fobj x := CD⁻¹ (F (AB.(to) x));
      fmap _ _ f := fmap[CD⁻¹] (fmap[F] (fmap[AB.(to)] f));
    |}.
    + proper; now rewrite X.
    + intros; now rewrite !fmap_id.
    + intros; now rewrite !fmap_comp.
Defined.

Global Program Instance fun_respects_iso :
  Proper (Isomorphism ==> Isomorphism ==> Isomorphism) (@Fun) :=
  λ A B AB C D CD, {|
    to := {|
      fobj F := fst (functor_respects_iso AB CD) F;
      fmap _ _ f := {|
        transform x := fmap[CD.(to)] (f (AB⁻¹ x))
      |}
    |};
    from := {|
      fobj F := snd (functor_respects_iso AB CD) F;
      fmap _ _ f := {|
        transform x := fmap[CD⁻¹] (f (AB.(to) x))
      |}
    |}
  |}.
(* to.fmap.naturality *)
Next Obligation. rewrite <- !fmap_comp. f_equiv. apply f. Defined.
(* to.fmap.naturality_sym *)
Next Obligation. rewrite <- !fmap_comp. f_equiv. apply f. Defined.
(* to.fmap_respects *)
Next Obligation. proper. f_equiv. apply X. Defined.
(* to.fmap_comp *)
Next Obligation. now rewrite <- fmap_comp. Defined.
(* from.fmap.naturality *)
Next Obligation. rewrite <- !fmap_comp. f_equiv. apply f. Defined.
(* from.fmap.naturality_sym *)
Next Obligation. rewrite <- !fmap_comp. f_equiv. apply f. Defined.
(* from.fmap_respects *)
Next Obligation. proper. f_equiv. apply X. Defined.
(* from.fmap_comp *)
Next Obligation. now rewrite <- fmap_comp. Defined.
(* iso_to_from.functor_equiv *)
Next Obligation. unshelve eexists.
  - (* iso *) intros F. construct.
    + (* to *) transform; simpl.
      * intros x. eapply compose.
        apply (iso_to_from CD). simpl.
        apply (fmap[CD.(to)]), (fmap[CD⁻¹]), (fmap[F]).
        apply (iso_to_from AB).
      * (* natuality *)
        destruct (iso_to_from AB) as [i1 e1];
        destruct (iso_to_from CD) as [i2 e2]; simpl in *.
        rewrite e1, !e2, !comp_assoc.
        rewrite iso_to_from, id_left.
        rewrite <- (comp_assoc (fmap[F] f)).
        rewrite iso_to_from, id_right.
        rewrite <- (comp_assoc (fmap[F] (i1 y))).
        rewrite iso_to_from, id_right.
        rewrite <- !fmap_comp, !comp_assoc.
        rewrite iso_to_from, id_left. reflexivity.
      * (* natuality_sym *)
        destruct (iso_to_from AB) as [i1 e1];
        destruct (iso_to_from CD) as [i2 e2]; simpl in *.
        rewrite e1, !e2, !comp_assoc.
        rewrite iso_to_from, id_left.
        rewrite <- (comp_assoc (fmap[F] f)).
        rewrite iso_to_from, id_right.
        rewrite <- (comp_assoc (fmap[F] (i1 y))).
        rewrite iso_to_from, id_right.
        rewrite <- !fmap_comp, !comp_assoc.
        rewrite iso_to_from, id_left. reflexivity.
    + (* from *) transform; simpl.
      * intros x. eapply compose; revgoals.
        apply (iso_to_from CD). simpl.
        apply (fmap[CD.(to)]), (fmap[CD⁻¹]), (fmap[F]).
        apply (iso_to_from AB).
      * (* natuality *)
        destruct (iso_to_from AB) as [i1 e1];
        destruct (iso_to_from CD) as [i2 e2]; simpl in *.
        rewrite e1, !e2, <- !comp_assoc. f_equiv.
        rewrite !fmap_comp, <- !comp_assoc. f_equiv.
        rewrite iso_to_from, id_right.
        rewrite (comp_assoc ((i2 (fobj[F] (fobj[AB.(to)] (fobj[AB⁻¹] x)))))).
        rewrite iso_to_from, id_left.
        rewrite (comp_assoc (i2 (fobj[F] y))).
        rewrite iso_to_from, id_left.
        rewrite <- !fmap_comp, iso_to_from, id_right. reflexivity.
      * (* natuality_sym *)
        destruct (iso_to_from AB) as [i1 e1];
        destruct (iso_to_from CD) as [i2 e2]; simpl in *.
        rewrite e1, !e2, <- !comp_assoc. f_equiv.
        rewrite !fmap_comp, <- !comp_assoc. f_equiv.
        rewrite iso_to_from, id_right.
        rewrite (comp_assoc ((i2 (fobj[F] (fobj[AB.(to)] (fobj[AB⁻¹] x)))))).
        rewrite iso_to_from, id_left.
        rewrite (comp_assoc (i2 (fobj[F] y))).
        rewrite iso_to_from, id_left.
        rewrite <- !fmap_comp, iso_to_from, id_right. reflexivity.
    + (* iso_to_from *) simpl.
      destruct (iso_to_from AB) as [i1 e1];
      destruct (iso_to_from CD) as [i2 e2]; simpl in *.
      rewrite !e2, !comp_assoc.
      rewrite iso_to_from, id_left.
      rewrite <- (comp_assoc (fmap[F] (i1 A0))).
      rewrite iso_to_from, id_right.
      rewrite <- fmap_comp.
      rewrite iso_to_from, fmap_id, id_left.
      rewrite iso_to_from. reflexivity.
    + (* iso_from_to *) simpl.
      destruct (iso_to_from AB) as [i1 e1];
      destruct (iso_to_from CD) as [i2 e2]; simpl in *.
      rewrite !e2, <- !comp_assoc; f_equiv.
      rewrite !comp_assoc; f_equiv.
      rewrite <- (comp_assoc (fmap[F] (i1 A0)⁻¹)).
      rewrite iso_to_from, id_right.
      rewrite <- (comp_assoc (fmap[F] (i1 A0)⁻¹)).
      rewrite iso_to_from, id_right.
      rewrite <- fmap_comp, iso_from_to, !fmap_id. reflexivity.
  - (* functor_equiv.iso.condition *) simpl.
    destruct (iso_to_from AB) as [i1 e1];
    destruct (iso_to_from CD) as [i2 e2]; simpl in *.
    intros F G n x. rewrite !e2.
    rewrite <- !comp_assoc; f_equiv.
    rewrite !comp_assoc; f_equiv.
    rewrite <- (comp_assoc (fmap[G] (i1 x)⁻¹)).
    rewrite iso_to_from, id_right.
    rewrite <- (comp_assoc (fmap[G] (i1 x)⁻¹ ∘ n x)).
    rewrite iso_to_from, id_right.
    destruct n; simpl. rewrite naturality.
    rewrite <- comp_assoc, <- fmap_comp.
    rewrite iso_from_to, fmap_id, id_right. reflexivity.
Defined.
(* iso_from_to.functor_setoid *)
Next Obligation. unshelve eexists.
  - (* iso *) intros F. construct.
    + (* to *) transform; simpl.
      * intros x. eapply compose.
        apply (iso_from_to CD). simpl.
        apply (fmap[CD⁻¹]), (fmap[CD.(to)]), (fmap[F]).
        apply (iso_from_to AB).
      * (* natuality *)
        destruct (iso_from_to AB) as [i1 e1];
        destruct (iso_from_to CD) as [i2 e2]; simpl in *.
        rewrite e1, !e2, !comp_assoc.
        rewrite iso_to_from, id_left.
        rewrite <- (comp_assoc (fmap[F] f)).
        rewrite iso_to_from, id_right.
        rewrite <- (comp_assoc (fmap[F] (i1 y))).
        rewrite iso_to_from, id_right.
        rewrite <- !fmap_comp, !comp_assoc.
        rewrite iso_to_from, id_left. reflexivity.
      * (* natuality_sym *)
        destruct (iso_from_to AB) as [i1 e1];
        destruct (iso_from_to CD) as [i2 e2]; simpl in *.
        rewrite e1, !e2, !comp_assoc.
        rewrite iso_to_from, id_left.
        rewrite <- (comp_assoc (fmap[F] f)).
        rewrite iso_to_from, id_right.
        rewrite <- (comp_assoc (fmap[F] (i1 y))).
        rewrite iso_to_from, id_right.
        rewrite <- !fmap_comp, !comp_assoc.
        rewrite iso_to_from, id_left. reflexivity.
    + (* from *) transform; simpl.
      * intros x. eapply compose; revgoals.
        apply (iso_from_to CD). simpl.
        apply (fmap[CD⁻¹]), (fmap[CD.(to)]), (fmap[F]).
        apply (iso_from_to AB).
      * (* natuality *)
        destruct (iso_from_to AB) as [i1 e1];
        destruct (iso_from_to CD) as [i2 e2]; simpl in *.
        rewrite e1, !e2, <- !comp_assoc. f_equiv.
        rewrite !fmap_comp, <- !comp_assoc. f_equiv.
        rewrite iso_to_from, id_right.
        rewrite (comp_assoc ((i2 (fobj[F] (fobj[AB⁻¹] (fobj[AB.(to)] x)))))).
        rewrite iso_to_from, id_left.
        rewrite (comp_assoc (i2 (fobj[F] y))).
        rewrite iso_to_from, id_left.
        rewrite <- !fmap_comp, iso_to_from, id_right. reflexivity.
      * (* natuality_sym *)
        destruct (iso_from_to AB) as [i1 e1];
        destruct (iso_from_to CD) as [i2 e2]; simpl in *.
        rewrite e1, !e2, <- !comp_assoc. f_equiv.
        rewrite !fmap_comp, <- !comp_assoc. f_equiv.
        rewrite iso_to_from, id_right.
        rewrite (comp_assoc ((i2 (fobj[F] (fobj[AB⁻¹] (fobj[AB.(to)] x)))))).
        rewrite iso_to_from, id_left.
        rewrite (comp_assoc (i2 (fobj[F] y))).
        rewrite iso_to_from, id_left.
        rewrite <- !fmap_comp, iso_to_from, id_right. reflexivity.
    + (* iso_to_from *) simpl.
      destruct (iso_from_to AB) as [i1 e1];
      destruct (iso_from_to CD) as [i2 e2]; simpl in *.
      rewrite !e2, !comp_assoc.
      rewrite iso_to_from, id_left.
      rewrite <- (comp_assoc (fmap[F] (i1 A0))).
      rewrite iso_to_from, id_right.
      rewrite <- fmap_comp.
      rewrite iso_to_from, fmap_id, id_left.
      rewrite iso_to_from. reflexivity.
    + (* iso_from_to *) simpl.
      destruct (iso_from_to AB) as [i1 e1];
      destruct (iso_from_to CD) as [i2 e2]; simpl in *.
      rewrite !e2, <- !comp_assoc; f_equiv.
      rewrite !comp_assoc; f_equiv.
      rewrite <- (comp_assoc (fmap[F] (i1 A0)⁻¹)).
      rewrite iso_to_from, id_right.
      rewrite <- (comp_assoc (fmap[F] (i1 A0)⁻¹)).
      rewrite iso_to_from, id_right.
      rewrite <- fmap_comp, iso_from_to, !fmap_id. reflexivity.
  - (* functor_setoid.iso.condition *) simpl.
    destruct (iso_from_to AB) as [i1 e1];
    destruct (iso_from_to CD) as [i2 e2]; simpl in *.
    intros F G n x. rewrite !e2.
    rewrite <- !comp_assoc; f_equiv.
    rewrite !comp_assoc; f_equiv.
    rewrite <- (comp_assoc (fmap[G] (i1 x)⁻¹)).
    rewrite iso_to_from, id_right.
    rewrite <- (comp_assoc (fmap[G] (i1 x)⁻¹ ∘ n x)).
    rewrite iso_to_from, id_right.
    destruct n; simpl. rewrite naturality.
    rewrite <- comp_assoc, <- fmap_comp.
    rewrite iso_from_to, fmap_id, id_right. reflexivity.
Defined.
