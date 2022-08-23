(*** Coq coding by choukh, Aug 2022 ***)

Set Warnings "-notation-overridden".
Set Implicit Arguments.
Set Universe Polymorphism.

Require Import Utf8_core ch3.
From Category Require Import Lib.Setoid.
From Category.Theory Require Import Functor.
From Category.Instance Require Import Cat Coq.

(* 4.1 *)
Check Functor.
Check Functor.Compose.

(* 4.2 *)
Example F : Gph ⟶ Coq.
Proof.
  apply (Build_Functor Gph Coq (@vertex) (@αᵥ)).
  congruence. firstorder.
  intros A B C [] [] x; reflexivity.
Qed.


