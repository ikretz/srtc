Require Import Coq.Program.Tactics.
Require Import List.
Import ListNotations.

From RT Require Import Pred Refn.

(* Primitive type of nats is a subtype of the base type *)
Lemma subtype_nat_base :
  forall n x y,
    subtype [] (TRefn x (PEq (PVar x) (PNat n))) (TBase y).
Proof.
  intros. constructor. constructor. firstorder.
Qed.

(* Every nat has base type *)
Lemma nat_has_base_type :
  forall n x, type_check [] (LNat n) (TBase x).
Proof.
  intros. eapply check_syn.
  - apply synth_nat.
  - apply subtype_nat_base with (x := 0).
Qed.

(* Nats that type check against a common nat are equal *)
Lemma nat_type_check_eq :
  forall n n' m x y,
    type_check [] (LNat n) (TRefn x (PEq (PVar x) (PNat m))) ->
    type_check [] (LNat n') (TRefn y (PEq (PVar y) (PNat m))) ->
    n = n'.
Proof.
  intros. inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H2; subst; clear H2.
  inversion H3; subst; clear H3.
  unfold valid in H. simpl in H.
  rewrite PeanoNat.Nat.eqb_refl in H.
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
  inversion H2; subst; clear H2.
  inversion H3; subst; clear H3.
  unfold valid in H0. simpl in H0.
  rewrite PeanoNat.Nat.eqb_refl in H0.
  compute in H. compute in H0.
  rewrite PeanoNat.Nat.eqb_refl in H.
  rewrite PeanoNat.Nat.eqb_refl in H0.
  assert (H1: PNat n = PNat n). { reflexivity. }
  assert (H2: PNat n' = PNat n'). { reflexivity. }
  apply H in H1. apply H0 in H2. rewrite <- H1 in H2.
  injection H2 as H2. symmetry. assumption.
Qed.

(* The primitive type of + is a subtype of + when the second argument
is restricted to a particular nat *)
Lemma subtype_add_prim_inc :
  forall n,
    subtype []
      (TFun 0 (TBase 0) (TFun 1 (TBase 1) (TRefn 2 (PEq (PVar 2) (PAdd (PVar 0) (PVar 1))))))
      (TFun 0 (TBase 0) (TFun 1 (TRefn 1 (PEq (PVar 1) (PNat n)))
                           (TRefn 2 (PEq (PVar 2) (PAdd (PVar 0) (PVar 1)))))).
Proof.
  intros. constructor.
  - apply subtype_refl.
  - rewrite same_var_change_type. constructor.
    + apply subtype_ctxt_extend.
      -- reflexivity.
      -- apply subtype_nat_base.
    + rewrite same_var_change_type. constructor.
      rewrite same_var_change_pred. constructor.
      constructor. constructor. compute. intros.
      rewrite H1. reflexivity.
Qed.

(* |- \x.\y.x+y : x{True} -> y{y = 1} -> z{z = x + y} *)
Example type_check_inc_refn :
  type_check []
    (LAbs 0 (LAbs 1 (LAdd (LVar 0) (LVar 1))))
    (TFun 0 (TBase 0) (TFun 1 (TRefn 1 (PEq (PVar 1) (PNat 1)))
                         (TRefn 2 (PEq (PVar 2) (PAdd (PVar 0) (PVar 1)))))).
Proof.
  eapply check_syn.
  - apply synth_add with (z := 2).
  - apply subtype_add_prim_inc.
Qed.

(* |- (x{True} -> y{y = n} -> z{z = x + y}) <: (x{True} -> y{y = n} -> z{z = x + n}) *)
Lemma subtype_inc_refn_nat :
  forall n,
    subtype []
      (TFun 0 (TBase 0) (TFun 1 (TRefn 1 (PEq (PVar 1) (PNat n)))
                           (TRefn 2 (PEq (PVar 2) (PAdd (PVar 0) (PVar 1))))))
      (TFun 0 (TBase 0) (TFun 1 (TRefn 1 (PEq (PVar 1) (PNat n)))
                           (TRefn 2 (PEq (PVar 2) (PAdd (PVar 0) (PNat n)))))).
Proof.
  intros. constructor.
  - apply subtype_refl.
  - simpl. constructor.
    + apply subtype_ctxt_extend.
      -- reflexivity.
      -- apply subtype_refl.
    + simpl; constructor. simpl; constructor.
      simpl; constructor. simpl; constructor.
      compute. intros. injection H0 as H0.
      rewrite H0 in H1. rewrite H1. reflexivity.
Qed.

(* |- \x.\y.x+y : x{True} -> y{y = 1} -> z{z = x + 1} *)
Lemma type_check_inc :
  type_check []
    (LAbs 0 (LAbs 1 (LAdd (LVar 0) (LVar 1))))
    (TFun 0 (TBase 0) (TFun 1 (TRefn 1 (PEq (PVar 1) (PNat 1)))
                         (TRefn 2 (PEq (PVar 2) (PAdd (PVar 0) (PNat 1)))))).
Proof.
  eapply check_syn.
  - apply synth_add with (z := 2).
  - constructor.
    + apply subtype_refl.
    + simpl. constructor.
      -- apply subtype_ctxt_extend.
         ++ reflexivity.
         ++ apply subtype_nat_base.
      -- simpl. constructor. constructor. constructor.
         constructor. compute. intros. injection H0 as H0.
         subst. rewrite H1. reflexivity.
Qed.
