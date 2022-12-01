Require Import List.
Import ListNotations.

From RT Require Import Pred.

(* Terms *)
Inductive term : Type :=
| LNat (n : nat)
| LVar (x : var)
| LAdd (t1 t2 : term)
| LBnd (x : var) (t1 t2 : term)
| LAbs (x : var) (t : term)
| LApp (t1 t2 : term).

(* Refinement types for terms *)
Inductive type : Type :=
(* Refined base type *)
| TRefn (x : var) (p : pred)
(* Dependent function type *)
| TFun (x : var) (T1 T2 : type).

(* Base type, nat *)
Definition TBase x := TRefn x (PBool true).

(* Capture-avoiding change of variables in types *)
Fixpoint change_var_type (T : type) (from to : var) : type :=
  match T with
  | TRefn x p =>
      if x =? from then T else TRefn x (change_var_pred p from to)
  | TFun x T1 T2 =>
      let T1' := change_var_type T1 from to in
      if x =? from then
        TFun x T1' T2
      else
        TFun x T1' (change_var_type T2 from to)
  end.

(* Contexts *)
Definition ctxt := list (var * type).

(* Query a context for the type of a variable *)
Fixpoint lookup (G : ctxt) (x : var) : option type :=
  match G with
  | [] => None
  | (y, T) :: G' =>
      if y =? x then Some T else lookup G' x
  end.

(* Constraint is valid *)
Definition valid c := cnst_prop c.

(* Context entails a constraint *)
Inductive entails : ctxt -> cnst -> Prop :=
| entails_emp :
  forall c, valid c -> entails [] c
| entails_ext :
  forall G x y p c,
    entails G (CImpl y (change_var_pred p x y) c) ->
    entails ((y, TRefn x p) :: G) c.

(* Subtyping rules *)
Inductive subtype : ctxt -> type -> type -> Prop :=
| subtype_refn :
  forall G x1 p1 x2 p2,
    entails G (CImpl x1 p1 (CPred (change_var_pred p2 x2 x1))) ->
    subtype G (TRefn x1 p1) (TRefn x2 p2)
| subtype_fun :
  forall G x1 S1 T1 x2 S2 T2,
    subtype G S2 S1 ->
    subtype ((x2, S2) :: G) (change_var_type T1 x1 x2) T2 ->
    subtype G (TFun x1 S1 T1) (TFun x2 S2 T2).

(* Bidirectional typing constructors *)
Inductive bidir : Type :=
| synth
| check.

(* Bidirectional typing rules for terms *)
Inductive type_judge : bidir -> ctxt -> term -> type -> Prop :=
| synth_var :
  forall G x T,
    lookup G x = Some T -> type_judge synth G (LVar x) T
| synth_nat :
  forall G n x,
    type_judge synth G (LNat n) (TRefn x (PEq (PVar x) (PNat n)))
| synth_add :
  forall G x y z,
    type_judge synth G
      (LAbs x (LAbs y (LAdd (LVar x) (LVar y))))
      (TFun x (TBase x) (TFun y (TBase y) (TRefn z (PEq (PVar z) (PAdd (PVar x) (PVar y))))))
| synth_app :
  forall G x y t T1 T2,
    type_judge synth G t (TFun x T1 T2) ->
    type_judge check G (LVar y) T1 ->
    type_judge synth G (LApp t (LVar y)) (change_var_type T2 x y)
| check_syn :
  forall G t T1 T2,
    type_judge synth G t T1 ->
    subtype G T1 T2 ->
    type_judge check G t T2
| check_abs :
  forall G x t T1 T2,
    type_judge check ((x, T1) :: G) t T2 ->
    type_judge check G (LAbs x t) (TFun x T1 T2)
| check_bnd :
  forall G x t1 t2 T1 T2,
    type_judge synth G t1 T1 ->
    type_judge check ((x, T1) :: G) t2 T2 ->
    type_judge check G (LBnd x t1 t2) T2.

Definition type_synth (G : ctxt) (t : term) (T : type) : Prop :=
  type_judge synth G t T.

Definition type_check (G : ctxt) (t : term) (T : type) : Prop :=
  type_judge check G t T.

(* Useful results *)

Lemma subtype_ctxt_extend :
  forall G x T T1 T2,
    lookup G x = None ->
    subtype G T1 T2 ->
    subtype ((x, T) :: G) T1 T2.
Admitted.

Lemma same_var_change_type : forall T x, change_var_type T x x = T.
Proof.
  intros. induction T.
  - simpl. destruct (x0 =? x) eqn:E0.
    + reflexivity.
    + rewrite same_var_change_pred. reflexivity.
  - simpl. destruct (x0 =? x) eqn:E0.
    + rewrite IHT1. reflexivity.
    + rewrite IHT1, IHT2. reflexivity.
Qed.

Lemma subtype_refl : forall T, subtype [] T T.
Proof.
  intros. induction T.
  - constructor. rewrite same_var_change_pred.
    constructor. compute. intros. assumption.
  - constructor.
    + assumption.
    + rewrite same_var_change_type.
      apply subtype_ctxt_extend.
         -- reflexivity.
         -- assumption.
Qed.
