Require Import Coq.ZArith.ZArith Coq.NArith.NArith Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.Assembly.QhasmCommon.
Require Export Bedrock.Word.
Require Export Crypto.Util.FixCoqMistakes.

Delimit Scope nword_scope with w.
Local Open Scope nword_scope.

Notation "& x" := (wordToN x) (at level 30) : nword_scope.
Notation "** x" := (NToWord _ x) (at level 30) : nword_scope.

Section Util.
  Definition convS {A B: Set} (x: A) (H: A = B): B :=
    eq_rect A (fun B0 : Set => B0) x B H.

  Definition high {k n: nat} (p: (k <= n)%nat) (w: word n): word k.
    refine (split1 k (n - k) (convS w _)).
    abstract (replace n with (k + (n - k)) by omega; intuition auto with arith).
  Defined.

  Definition low {k n: nat} (p: (k <= n)%nat) (w: word n): word k.
    refine (split2 (n - k) k (convS w _)).
    abstract (replace n with (k + (n - k)) by omega; intuition auto with zarith).
  Defined.

  Definition extend {k n: nat} (p: (k <= n)%nat) (w: word k): word n.
    refine (convS (zext w (n - k)) _).
    abstract (replace (k + (n - k)) with n by omega; intuition).
  Defined.

  Definition shiftr {n} (w: word n) (k: nat): word n :=
    match (le_dec k n) with
    | left p => extend p (high p w)
    | right _ => wzero n
    end.

  Definition mask {n} (k: nat) (w: word n): word n :=
    match (le_dec k n) with
    | left p => extend p (low p w)
    | right _ => w
    end.

  Definition overflows (n: nat) (x: N) :
      {(x >= Npow2 n)%N} + {(x < Npow2 n)%N}.
    refine (
      let c := (x ?= Npow2 n)%N in
      match c as c' return c = c' -> _ with
      | Lt => fun _ => right _
      | _ => fun _ => left _
      end eq_refl); abstract (
        unfold c in *; unfold N.lt, N.ge;
        repeat match goal with
        | [ H: (_ ?= _)%N = _ |- _] =>
          rewrite H; intuition; try inversion H
        | [ H: Eq = _ |- _] => inversion H
        | [ H: Gt = _ |- _] => inversion H
        | [ H: Lt = _ |- _] => inversion H
        end).
  Defined.

  Definition break {n} (m: nat) (x: word n): word m * word (n - m).
    refine match (le_dec m n) with
    | left p => (extend _ (low p x), extend _ (@high (n - m) n _ x))
    | right p => (extend _ x, _)
    end; try abstract intuition auto with zarith.

    replace (n - m) with O by abstract omega; exact WO.
  Defined.

  Definition addWithCarry {n} (x y: word n) (c: bool): word n :=
    x ^+ y ^+ (natToWord _ (if c then 1 else 0)).

  Definition omap {A B} (x: option A) (f: A -> option B) :=
    match x with | Some y => f y | _ => None end.

  Notation "A <- X ; B" := (omap X (fun A => B)) (at level 70, right associativity).
End Util.

Close Scope nword_scope.
