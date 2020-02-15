Require Import Coq.ZArith.ZArith.
Require Import MirrorCore.Lambda.ExprCore.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.AutoSetoidRewriteRtac.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Instantiate.

Set Implicit Arguments.
Local Set Boolean Equality Schemes.
Inductive typ := rNAT | rZ | rPROD (_ _ : typ) | rARROW (_ _ : typ) | rPROP.
Inductive func := Z_ADD | NAT_RECT | LET_IN | PAIR | PROD_RECT | rZ0 | rO | rS.

Ltac fin_falso :=
  intros; exfalso; (apply Bool.diff_false_true + apply Bool.diff_true_false); assumption.

Lemma typ_dec_lb x y : x = y -> typ_beq x y = true.
Proof.
  intro; subst y; induction x; cbn; try reflexivity.
  all: do 2 edestruct typ_beq; cbn in *; try reflexivity; fin_falso.
Defined.
Lemma typ_dec_bl : forall x y, typ_beq x y = true -> x = y.
Proof.
  induction x, y; cbn in *; intros; try reflexivity; try fin_falso.
  all: f_equal; match goal with H : _ |- _ => apply H end.
  all: do 2 edestruct typ_beq; cbn in *; try reflexivity; try fin_falso.
Defined.

Lemma func_dec_lb x y : x = y -> func_beq x y = true.
Proof. intro; subst y; destruct x; reflexivity. Defined.
Lemma func_dec_bl x y : func_beq x y = true -> x = y.
Proof. destruct x, y; try reflexivity; cbn; try fin_falso. Defined.

Definition typ_eq_dec (x y : typ) : {x = y} + {x <> y}
  := (if typ_beq x y as beq return typ_beq x y = beq -> _
      then fun pf => left (typ_dec_bl _ _ pf)
      else fun pf => right (fun H => Bool.diff_true_false (eq_trans (eq_sym (typ_dec_lb H)) pf)))
       eq_refl.

Definition func_eq_dec (x y : func) : {x = y} + {x <> y}
  := (if func_beq x y as beq return func_beq x y = beq -> _
      then fun pf => left (func_dec_bl _ _ pf)
      else fun pf => right (fun H => Bool.diff_true_false (eq_trans (eq_sym (func_dec_lb H)) pf)))
       eq_refl.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
Bind Scope typ_scope with typ.
Infix "*" := rPROD : typ_scope.
Infix "->" := rARROW : typ_scope.

Fixpoint typD (t : typ) : Type
  := match t with
     | rPROP => Prop
     | rNAT => nat
     | rZ => Z
     | rPROD a b => typD a * typD b
     | rARROW s d => typD s -> typD d
     end%type.

Definition typ_of_func (f : func) : typ
  := match f with
     | Z_ADD => rZ -> rZ -> rZ
     | NAT_RECT => (rZ * rZ -> rZ) -> (rNAT -> (rZ * rZ -> rZ) -> (rZ * rZ -> rZ)) -> rNAT -> (rZ * rZ -> rZ)
     | LET_IN => rZ -> (rZ -> rZ) -> rZ
     | PAIR => rZ -> rZ -> rZ * rZ
     | PROD_RECT => (rZ -> rZ -> rZ) -> rZ * rZ -> rZ
     | rZ0 => rZ
     | rO => rNAT
     | rS => rNAT -> rNAT
     end%typ.

Definition Let_In {A P} (x : A) (f : forall x : A, P x) : P x := let y := x in f y.

Definition funcD (f : func) : typD (typ_of_func f)
  := match f with
     | Z_ADD => Z.add
     | NAT_RECT => @nat_rect _
     | LET_IN => @Let_In _ _
     | PAIR => @pair _ _
     | PROD_RECT => @prod_rect _ _ _
     | rZ0 => Z0
     | rO => O
     | rS => S
     end.

Instance RelDec_eq_typ : RelDec (@eq typ) := { rel_dec := typ_beq }.
Instance RelDec_eq_func : RelDec (@eq func) := { rel_dec := func_beq }.
Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ.
Proof. constructor; split; auto using typ_dec_bl, typ_dec_lb. Qed.
Instance RelDec_Correct_eq_func : RelDec_Correct RelDec_eq_func.
Proof. constructor; split; auto using func_dec_bl, func_dec_lb. Qed.

Inductive tyAcc' : typ -> typ -> Prop :=
| rARROWL : forall a b, tyAcc' a (rARROW a b)
| rARROWR : forall a b, tyAcc' b (rARROW a b).

Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc'
; type_cast := fun a b => match typ_eq_dec a b with
                            | left pf => Some pf
                            | _ => None
                          end
}.

Instance RTypeOk_typ : @RTypeOk typ _.
Proof.
  eapply makeRTypeOk.
  { red.
    induction a; constructor; inversion 1.
    subst; auto.
    subst; auto. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x x).
    f_equal. compute.
    uip_all. reflexivity. congruence. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x y); try congruence. }
Qed.

Instance Typ2_rARROW : Typ2 _ Fun :=
{ typ2 := rARROW
; typ2_cast := fun _ _ => eq_refl
; typ2_match :=
    fun T t tr =>
      match t as t return T (TypesI.typD t) -> T (TypesI.typD t) with
        | rARROW a b => fun _ => tr a b
        | _ => fun fa => fa
      end
}.

Instance Typ2Ok_rARROW : Typ2Ok Typ2_rARROW.
Proof.
  constructor.
  { reflexivity. }
  { apply rARROWL. }
  { intros; apply rARROWR. }
  { inversion 1; subst; unfold Rty; auto. }
  { destruct x; simpl; eauto.
    left; do 2 eexists; exists eq_refl. reflexivity. }
  { destruct pf. reflexivity. }
Qed.

Instance Typ0_Prop : Typ0 _ Prop :=
{| typ0 := rPROP
 ; typ0_cast := eq_refl
 ; typ0_match := fun T t =>
                   match t with
                     | rPROP => fun tr _ => tr
                     | _ => fun _ fa => fa
                   end
|}.
Instance RSym_func : RSym func :=
{ typeof_sym f := Some (typ_of_func f)
; symD := funcD
; sym_eqb := fun a b => Some (a ?[ eq ] b)
}.


Instance RSymOk_func : RSymOk RSym_func.
{ constructor.
  intros. simpl. consider (a ?[ eq ] b); auto. }
Qed.

Local Notation expr := (expr typ func).
Local Notation App2 f x := (App (App f x)).
Local Notation App3 f x y := (App2 (App f x) y).
Local Notation App4 f x y z := (App3 (App f x) y z).

Notation E := expr (only parsing).
Instance Expr_E : Expr _ E := Expr_expr.
Definition subst : Type := FMapSubst.SUBST.raw E.
Instance Subst_subst : Subst subst E := FMapSubst.SUBST.Subst_subst _.
Instance SubstUpdate_subst : SubstUpdate subst E := @FMapSubst.SUBST.SubstUpdate_subst _ _ _ _.

(*Let eq_nat (a b : E) : E := Inj (Eq rZ) @ a @ b.*)
Local Notation plus a b := (App2 (Inj Z_ADD) a b).

Definition MAKE_LETS_DEF (n : nat) (acc : expr) :=
  App4
    (Inj NAT_RECT)
    (App (Inj PROD_RECT)
         ((Abs (* v : Z *) rZ)
            ((Abs (* acc : Z *) rZ)
               (let v := Var 1 in
                let acc := Var 0 in
                App2 (Inj Z_ADD) (App2 (Inj Z_ADD) acc acc) v))))
    ((Abs (* _ : nat *) rNAT)
       ((Abs (* rec : Z * Z -> Z *) (rARROW (rPROD rZ rZ) rZ))
          (let rec : expr := Var 0 in
           App
             (Inj PROD_RECT)
             ((Abs (* v : Z *) rZ)
                ((Abs (* acc : Z *) rZ)
                   (let rec : expr := Var 2 in
                    let v := Var 1 in
                    let acc := Var 0 in
                    App2 (Inj LET_IN)
                         (App2 (Inj Z_ADD) (App2 (Inj Z_ADD) acc acc) v)
                         ((Abs (* acc : Z *) rZ)
                            (let rec := Var 3 in
                             let v := Var 2 in
                             let acc : expr := Var 1 in
                             let acc := Var 0 in
                             App rec (App2 (Inj PAIR) v acc)))))))))
    (nat_rect _ (Inj rO) (fun _ rec => App (Inj rS) rec) n)
    (App2 (Inj PAIR) (Inj rZ0) acc).

(* forall n, n + 0 = n *)
Definition RW1 : RW typ E subst :=
{| lem := {| Lemma.vars := rZ :: nil
           ; Lemma.premises := nil
           ; Lemma.concl := (rZ, plus (Var 0) (Inj rZ0), Var 0) |}
 ; side_solver := use_list nil
 |}.
(* The reference RW was not found in the current environment. *)

Goal forall acc, exprD nil nil rZ (MAKE_LETS_DEF 5 acc) = exprD nil nil rZ acc.
