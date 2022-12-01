Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Lia.
Require Export Nat.

(* Variables *)
Definition var := nat.

(* Predicate expressions *)
Inductive expr : Type :=
| PNat (n : nat)
| PVar (x : var)
| PAdd (e1 e2 : expr).

(* Change of variables in exprs *)
Fixpoint change_var_expr (e : expr) (from to : var) : expr :=
  match e with
  | PNat _ => e
  | PVar x =>
      if x =? from then PVar to else e
  | PAdd e1 e2 =>
      PAdd (change_var_expr e1 from to) (change_var_expr e2 from to)
  end.

(* Substitute a nat for a var in an expr *)
Fixpoint subst_expr (e : expr) (from : var) (to : nat) : expr :=
  match e with
  | PNat _ => e
  | PVar x =>
      if x =? from then PNat to else e
  | PAdd e1 e2 =>
      PAdd (subst_expr e1 from to) (subst_expr e2 from to)
  end.

(* Simplify an expr *)
Fixpoint simpl_expr (e : expr) : expr :=
  match e with
  | PAdd e1 e2 =>
      let e1' := simpl_expr e1 in
      let e2' := simpl_expr e2 in
      match e1', e2' with
      | PNat n, PNat m => PNat (n + m)
      | _, _ => PAdd e1' e2'
      end
  | _ => e
  end.

(* Predicates *)
Inductive pred : Type :=
| PBool (b : bool)
| PEq (e1 e2 : expr)
| PAnd (p1 p2 : pred)
| POr (p1 p2 : pred).

(* Change of variables in preds *)
Fixpoint change_var_pred (p : pred) (from to : var) : pred :=
  match p with
  | PBool _ => p
  | PEq e1 e2 =>
      PEq (change_var_expr e1 from to) (change_var_expr e2 from to)
  | PAnd p1 p2 =>
      PAnd (change_var_pred p1 from to) (change_var_pred p2 from to)
  | POr p1 p2 =>
      POr (change_var_pred p1 from to) (change_var_pred p2 from to)
  end.

(* Substitute a nat for a var in a pred *)
Fixpoint subst_pred (p : pred) (from : var) (to : nat) : pred :=
  match p with
  | PBool _ => p
  | PEq e1 e2 =>
      PEq (subst_expr e1 from to) (subst_expr e2 from to)
  | PAnd p1 p2 =>
      PAnd (subst_pred p1 from to) (subst_pred p2 from to)
  | POr p1 p2 =>
      POr (subst_pred p1 from to) (subst_pred p2 from to)
  end.

(* Simplify a pred *)
Fixpoint simpl_pred (p : pred) : pred :=
  match p with
  | PBool _ => p
  | PEq e1 e2 =>
      PEq (simpl_expr e1) (simpl_expr e2)
  | PAnd p1 p2 =>
      PAnd (simpl_pred p1) (simpl_pred p2)
  | POr p1 p2 =>
      POr (simpl_pred p1) (simpl_pred p2)
  end.

(* Convert a pred into its equivalent Prop *)
Fixpoint pred_prop (p : pred) : Prop :=
  match p with
  | PBool true => True
  | PBool false => False
  | PEq e1 e2 => e1 = e2
  | PAnd p1 p2 => (pred_prop p1) /\ (pred_prop p2)
  | POr p1 p2 => (pred_prop p1) \/ (pred_prop p2)
  end.

(* Substitution satisfies a simplified predicate *)
Definition sat_pred p x n := pred_prop (simpl_pred (subst_pred p x n)).

(* Constraints *)
Inductive cnst : Type :=
| CPred (p : pred)
| CAnd (c1 c2 : cnst)
| CImpl (x : var) (p : pred) (c : cnst).

(* Substitute a nat for a var in a cnst *)
Fixpoint subst_cnst (c : cnst) (from : var) (to : nat) : cnst :=
  match c with
  | CPred p =>
      CPred (subst_pred p from to)
  | CAnd c1 c2 =>
      CAnd (subst_cnst c1 from to) (subst_cnst c2 from to)
  | CImpl x p c' =>
      if x =? from then
        c
      else
        CImpl x (subst_pred p from to) (subst_cnst c' from to)
  end.

(* Height of a cnst, needed to prove termination below *)
Fixpoint cnst_height (c : cnst) : nat :=
  match c with
  | CPred _ => 1
  | CAnd c1 c2 =>
      1 + max (cnst_height c1) (cnst_height c2)
  | CImpl x p c' => 1 + cnst_height c'
  end.

(* Convert a cnst into its equivalent Prop *)
Program Fixpoint cnst_prop (c : cnst) {measure (cnst_height c)} : Prop :=
  match c with
  | CPred p => pred_prop (simpl_pred p)
  | CAnd c1 c2 =>
      (cnst_prop c1) /\ (cnst_prop c2)
  | CImpl x p c' =>
      forall n, sat_pred p x n -> cnst_prop (subst_cnst c' x n)
  end.
Next Obligation.
  destruct c1; simpl; destruct c2; simpl; lia.
Qed.
Next Obligation.
  destruct c2; simpl; destruct c1; simpl; lia.
Qed.
Next Obligation.
  assert (H: forall c y m, cnst_height (subst_cnst c y m) = cnst_height c).
  {
    intros. induction c; simpl.
    - reflexivity.
    - rewrite IHc1, IHc2. reflexivity.
    - destruct (x0 =? y); simpl.
      + reflexivity.
      + rewrite IHc. reflexivity.
  }
  simpl. rewrite H. lia.
Qed.

(* Useful results *)

Lemma same_var_change_expr : forall e x, change_var_expr e x x = e.
Proof.
  intros. induction e.
  - reflexivity.
  - simpl. destruct (x0 =? x) eqn:E0.
    + apply PeanoNat.Nat.eqb_eq in E0.
      rewrite E0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHe1, IHe2. reflexivity.
Qed.

Lemma same_var_change_pred : forall p x, change_var_pred p x x = p.
Proof.
  intros. induction p.
  - reflexivity.
  - simpl. repeat rewrite same_var_change_expr. reflexivity.
  - simpl. rewrite IHp1, IHp2. reflexivity.
  - simpl. rewrite IHp1, IHp2. reflexivity.
Qed.
