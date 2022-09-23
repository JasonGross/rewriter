(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+undeclared-scope,+deprecated-typeclasses-transparency-without-locality,unsupported-attributes" "-R" "src/Rewriter" "Rewriter" "-I" "src/Rewriter/Util/plugins" "-top" "Rewriter.Rewriter.Examples" "-native-compiler" "ondemand" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 104176 lines to 97527 lines, then from 97560 lines to 3537 lines, then from 3550 lines to 3708 lines, then from 3713 lines to 3538 lines, then from 3551 lines to 3718 lines, then from 3723 lines to 3540 lines, then from 3553 lines to 3711 lines, then from 3716 lines to 3542 lines, then from 3555 lines to 3711 lines, then from 3716 lines to 3574 lines, then from 3587 lines to 7609 lines, then from 7612 lines to 3623 lines, then from 3636 lines to 5049 lines, then from 5052 lines to 5032 lines *)
(* coqc version 8.15.0 compiled with OCaml 4.11.2
   coqtop version 8.15.0
   Expected coqc runtime on this file: 3.452 sec *)
Require Coq.ZArith.ZArith.
Require Coq.FSets.FMapPositive.
Require Coq.Bool.Bool.
Require Coq.Lists.List.
Require Coq.Classes.Morphisms.
Require Coq.Relations.Relation_Definitions.
Require Ltac2.Init.
Require Coq.Classes.RelationClasses.
Require Rewriter.Util.IffT.
Require Rewriter.Util.Isomorphism.
Require Rewriter.Util.HProp.
Require Rewriter.Util.Equality.
Require Rewriter.Util.GlobalSettings.
Require Rewriter.Util.PrimitiveProd.
Require Rewriter.Util.PrimitiveHList.
Require Rewriter.Util.InductiveHList.
Require Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Notations.
Require Rewriter.Language.PreCommon.
Require Rewriter.Util.Tactics.GetGoal.
Require Rewriter.Util.LetIn.
Require Coq.Lists.SetoidList.
Require Coq.micromega.Lia.
Require Coq.Arith.Peano_dec.
Require Coq.Arith.Arith.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.Logic.Eqdep_dec.
Require Coq.NArith.NArith.
Require Rewriter.Util.NatUtil.
Require Coq.Numbers.BinNums.
Require Rewriter.Util.Pointed.
Require Coq.Setoids.Setoid.
Require Rewriter.Util.Prod.
Require Rewriter.Util.Sigma.
Require Coq.ZArith.BinInt.
Require Coq.ZArith.ZArith_dec.
Require Coq.NArith.BinNat.
Require Rewriter.Util.Decidable.
Require Rewriter.Util.Tactics.Head.
Require Rewriter.Util.Tactics.BreakMatch.
Require Rewriter.Util.Tactics.DestructHyps.
Require Rewriter.Util.Tactics.DestructHead.
Require Rewriter.Util.Option.
Require Rewriter.Util.Tactics.SpecializeBy.
Require Rewriter.Util.Tactics.Test.
Require Rewriter.Util.Tactics.Not.
Require Rewriter.Util.Tactics.DoWithHyp.
Require Rewriter.Util.Tactics.RewriteHyp.
Require Rewriter.Util.Tactics.ConstrFail.
Require Rewriter.Util.Tactics.SplitInContext.
Require Rewriter.Util.ListUtil.
Require Rewriter.Util.OptionList.
Require Rewriter.Util.CPSNotations.
Require Coq.Classes.CMorphisms.
Require Coq.Strings.String.
Require Coq.Strings.Ascii.
Require Rewriter.Util.ListUtil.SetoidList.
Require Rewriter.Util.Tactics.Contains.
Require Rewriter.Util.Tactics.SetoidSubst.
Require Rewriter.Util.Sum.
Require Rewriter.Util.Comparison.
Require Rewriter.Util.Bool.Reflect.
Require Rewriter.Util.Bool.
Require Rewriter.Language.Language.
Require Coq.Relations.Relations.
Require Rewriter.Util.Tactics.FindHyp.
Require Rewriter.Util.Tactics.UniquePose.
Require Rewriter.Util.Tactics.SpecializeAllWays.
Require Rewriter.Language.Inversion.
Require Rewriter.Util.ListUtil.Forall.
Require Rewriter.Util.Logic.ProdForall.
Require Rewriter.Language.Wf.
Require Rewriter.Language.IdentifiersBasicLibrary.
Require Ltac2.Ltac2.
Require Ltac2.Bool.
Require Ltac2.Printf.
Require Rewriter.Language.Pre.
Require Rewriter.Util.Tactics.RunTacticAsConstr.
Require Rewriter.Util.Tactics.DebugPrint.
Require Rewriter.Util.Tactics2.List.
Require Rewriter.Util.Tactics2.Ltac1.
Require Rewriter.Util.Tactics2.Message.
Require Ltac2.Ltac1.
Require Rewriter.Util.Tactics2.Ident.
Require Rewriter.Util.Tactics2.Char.
Require Rewriter.Util.Tactics2.String.
Require Rewriter.Util.Tactics2.Constr.Unsafe.MakeAbbreviations.
Require Rewriter.Language.Reify.
Require Rewriter.Util.TypeList.
Require Rewriter.Util.Tactics.HeadUnderBinders.
Require Rewriter.Util.Tactics.PrintContext.
Require Rewriter.Util.Tactics.PrintGoal.
Require Rewriter.Util.Tactics.EvarNormalize.
Require Rewriter.Util.Tactics.ClearFree.
Require Rewriter.Util.Tactics.CacheTerm.
Require Rewriter.Util.Tactics2.Notations.
Require Rewriter.Language.IdentifiersBasicGenerate.
Require Coq.MSets.MSetPositive.
Require Rewriter.Language.UnderLets.
Require Coq.derive.Derive.
Require Rewriter.Util.PrimitiveSigma.
Require Rewriter.Language.IdentifiersLibrary.
Require Rewriter.Rewriter.Rewriter.
Require Rewriter.Util.Tactics2.Head.
Require Rewriter.Util.Tactics2.Constr.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export ProofsCommon.
Import Rewriter.Language.Language.
Import Rewriter.Language.IdentifiersBasicLibrary.
Module Export Compilers.
  Import Language.Compilers.
  Import Language.Wf.Compilers.

  Module Import RewriteRules.

    Module Import WfTactics.
      End WfTactics.

    Module Export GoalType.
      Import Compilers.Basic.GoalType.
      Import Compilers.Classes.

      Record VerifiedRewriter :=
        {
          exprInfo : ExprInfoT;
          exprReifyInfo : ExprReifyInfoT;
          optsT : Type;
          default_opts : optsT;

          Rewrite : forall (opts : optsT) {t} (e : expr.Expr (ident:=ident) t), expr.Expr (ident:=ident) t;
          Wf_Rewrite : forall opts {t} e (Hwf : Wf e), Wf (@Rewrite opts t e);
          Interp_Rewrite opts {t} e
          : forall (Hwf : Wf e), expr.Interp ident_interp (@Rewrite opts t e) == expr.Interp ident_interp e;

          check_wf : forall {t}, expr.Expr (ident:=ident) t -> bool;
          generalize_for_wf : forall {t}, expr.Expr (ident:=ident) t -> expr.Expr (ident:=ident) t;
          prove_Wf : forall {t} (e : expr.Expr (ident:=ident) t), (e = generalize_for_wf e /\ check_wf e = true) -> expr.Wf e;
        }.

      Definition VerifiedRewriter_with_ind_args
                 (scraped_data : ScrapedData.t)
                 (var_like_idents : InductiveHList.hlist)
                 (base : Type)
                 (ident : type.type (base.type base) -> Type)
                 (raw_ident : Type)
                 (pattern_ident : type.type (pattern.base.type base) -> Type)
                 (include_interp : bool)
                 (skip_early_reduction skip_early_reduction_no_dtree : bool)
                 {rewrite_rulesT} (rules_proofs : PrimitiveHList.hlist (@snd bool Prop) rewrite_rulesT)
        := VerifiedRewriter.

Module Rewriter_DOT_Rewriter_DOT_Reify_WRAPPED.
Module Reify.
Import Coq.ZArith.ZArith.
Import Coq.FSets.FMapPositive.
Import Coq.MSets.MSetPositive.
Import Coq.Lists.List.
Import Ltac2.Ltac2.
Import Ltac2.Printf.
Import Rewriter.Util.Option.
Import Rewriter.Util.OptionList.
Import Rewriter.Util.Bool.Reflect.
Import Rewriter.Language.Language.
Import Rewriter.Language.Reify.
Import Rewriter.Language.UnderLets.
Import Rewriter.Language.IdentifiersLibrary.
Import Rewriter.Language.IdentifiersBasicGenerate.
 
Import Rewriter.Rewriter.Rewriter.
Import Rewriter.Util.LetIn.
Import Rewriter.Util.Tactics.BreakMatch.
Import Rewriter.Util.Tactics.DestructHead.
Import Rewriter.Util.Tactics.ConstrFail.
Import Rewriter.Util.Tactics.Head.
Import Rewriter.Util.Tactics.CacheTerm.
Import Rewriter.Util.Tactics.DebugPrint.
Import Rewriter.Util.CPSNotations.
Import Rewriter.Util.Notations.
Import Rewriter.Util.Tactics2.Head.
Import Rewriter.Util.Tactics2.Constr.Unsafe.MakeAbbreviations.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

Local Set Primitive Projections.
Local Set Default Proof Mode "Classic".
Import EqNotations.
Module Compilers.
  Export Language.Compilers.
  Export Language.Reify.Compilers.
  Export UnderLets.Compilers.
  Export IdentifiersLibrary.Compilers.
  Export IdentifiersBasicGenerate.Compilers.
  Import invert_expr.
  Export Rewriter.Compilers.

  Module RewriteRules.
    Export Rewriter.Compilers.RewriteRules.

    Module Reify.
      Export Rewriter.Compilers.RewriteRules.Reify.
      Import Compile.
      Local Notation EvarMap := pattern.EvarMap.
      Local Notation EvarMap_at base := (pattern.EvarMap_at base).

      Section with_var.
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation pattern_base_type := (pattern.base.type base).
        Local Notation type := (type.type base_type).
        Local Notation ptype := (type.type pattern_base_type).
        Context {try_make_transport_base_cps : type.try_make_transport_cpsT base}
                {ident var : type -> Type}
                {pident : ptype -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_type_of_list_arg_types_beq : forall t idc, type_of_list (pident_arg_types t idc) -> type_of_list (pident_arg_types t idc) -> bool)
                (pident_of_typed_ident : forall t, ident t -> pident (pattern.type.relax t))
                (pident_arg_types_of_typed_ident : forall t (idc : ident t), type_of_list (pident_arg_types _ (pident_of_typed_ident t idc)))
                (reflect_ident_iota : forall t (idc : ident t), option (@value base_type ident var t)).

        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation pattern := (@pattern.pattern base pident).
        Local Notation value := (@Compile.value base_type ident var).
        Local Notation value_with_lets := (@Compile.value_with_lets base_type ident var).
        Local Notation UnderLets := (UnderLets.UnderLets base_type ident var).
        Local Notation reify_expr_beta_iota := (@reify_expr_beta_iota base ident var reflect_ident_iota).
        Local Notation unification_resultT' := (@unification_resultT' base pident pident_arg_types).
        Local Notation with_unif_rewrite_ruleTP_gen' := (@with_unif_rewrite_ruleTP_gen' base ident var pident pident_arg_types value).
        Local Notation lam_unification_resultT' := (@lam_unification_resultT' base pident pident_arg_types).
        Local Notation expr_value_to_rewrite_rule_replacement := (@expr_value_to_rewrite_rule_replacement base ident var reflect_ident_iota).

        Local Notation expr_maybe_do_again should_do_again
          := (@expr.expr base_type ident (if should_do_again then value else var)).

        Inductive pattern_of_expr_error_messages {t} :=
        | ILLEGAL_ABS_ON_LHS (e : @expr.expr base_type ident (fun _ => positive) t)
        | ILLEGAL_LET_IN_ON_LHS (e : @expr.expr base_type ident (fun _ => positive) t)
        .

        Fixpoint pattern_of_expr (var' := fun _ => positive) evm (invalid : forall t, @pattern_of_expr_error_messages t -> { p : pattern (pattern.type.relax t) & @unification_resultT' var' _ p evm })
                 {t} (e : @expr.expr base_type ident var' t)
          : { p : pattern (pattern.type.relax t) & @unification_resultT' var' _ p evm }
          := match e in expr.expr t return { p : pattern (pattern.type.relax t) & @unification_resultT' var' _ p evm } with
             | expr.Ident t idc
               => existT _ (pattern.Ident (pident_of_typed_ident _ idc))
                         (pident_arg_types_of_typed_ident _ idc)
             | expr.Var t v
               => existT _ (pattern.Wildcard _) v
             | expr.App s d f x
               => let 'existT fp fv := @pattern_of_expr evm invalid _ f in
                  let 'existT xp xv := @pattern_of_expr evm invalid _ x in
                  existT _ (pattern.App fp xp)
                         (fv, xv)
             | expr.Abs _ _ _ as e
               => invalid _ (ILLEGAL_ABS_ON_LHS e)
             | expr.LetIn _ _ _ _ as e
               => invalid _ (ILLEGAL_LET_IN_ON_LHS e)
             end.

        Fixpoint pair'_unification_resultT' {A evm t p}
          : @unification_resultT' (fun _ => positive) t p evm -> @unification_resultT' value t p evm -> PositiveMap.t { t : _ & value t } * (A -> list bool) -> PositiveMap.t { t : _ & value t } * (A -> list bool)
          := match p return @unification_resultT' (fun _ => positive) _ p evm -> @unification_resultT' value _ p evm -> PositiveMap.t { t : _ & value t } * (A -> list bool) -> PositiveMap.t { t : _ & value t } * (A -> list bool) with
             | pattern.Wildcard t => fun p v '(m, l) => (PositiveMap.add p (existT value _ v) m, l)
             | pattern.Ident t idc => fun v1 v2 '(m, l) => (m, fun a => pident_type_of_list_arg_types_beq t idc v2 v1 :: l a)
             | pattern.App _ _ F X
               => fun x y '(m, l)
                  => let '(m, l) := @pair'_unification_resultT' _ _ _ F (fst x) (fst y) (m, l) in
                     let '(m, l) := @pair'_unification_resultT' _ _ _ X (snd x) (snd y) (m, l) in
                     (m, l)
             end.

        Inductive expr_pos_to_expr_value_error_message :=
        | MISSING_VAR (_ : positive * type * PositiveMap.t { t : _ & value t })
        .

        Fixpoint expr_pos_to_expr_value
                 (invalid : forall t, expr_pos_to_expr_value_error_message -> @expr.expr base_type ident value t)
                 {t} (e : @expr.expr base_type ident (fun _ => positive) t) (m : PositiveMap.t { t : _ & value t }) (cur_i : positive)
          : @expr.expr base_type ident value t
          := match e in expr.expr t return expr.expr t with
             | expr.Ident t idc => expr.Ident idc
             | expr.App s d f x
               => expr.App (@expr_pos_to_expr_value invalid _ f m cur_i)
                           (@expr_pos_to_expr_value invalid _ x m cur_i)
             | expr.Var t v
               => match option_map
                          (fun tv => type.try_transport value _ t (projT2 tv))
                          (PositiveMap.find v m) with
                  | Some (Some res) => expr.Var res
                  | Some None | None => invalid _ (MISSING_VAR (v, t, m))
                  end
             | expr.Abs s d f
               => expr.Abs (fun v => @expr_pos_to_expr_value invalid _ (f cur_i) (PositiveMap.add cur_i (existT value _ v) m) (Pos.succ cur_i))
             | expr.LetIn A B x f
               => expr.LetIn (@expr_pos_to_expr_value invalid _ x m cur_i)
                             (fun v => @expr_pos_to_expr_value invalid _ (f cur_i) (PositiveMap.add cur_i (existT value _ v) m) (Pos.succ cur_i))
             end.

        Inductive lookup_gets_inlined_error_messages :=
        | NO_SUCH_EXPRESSION_TO_CHECK (p : positive) (m : PositiveMap.t { t : _ & value t })
        | TYPE_IS_NOT_BASE (p : positive) (m : PositiveMap.t { t : _ & value t }) (t : type).

        Definition lookup_expr_gets_inlined
                   (invalid : lookup_gets_inlined_error_messages -> bool)
                   (gets_inlined : forall t, value (type.base t) -> bool)
                   (m : PositiveMap.t { t : _ & value t })
                   (p : positive)
          : bool
          := Eval cbv -[value] in
              match PositiveMap.find p m with
              | Some (existT t e)
                => match t return value t -> _ with
                   | type.base t => gets_inlined t
                   | _ => fun _ => invalid (TYPE_IS_NOT_BASE p m t)
                   end e
              | None => invalid (NO_SUCH_EXPRESSION_TO_CHECK p m)
              end.

        Definition expr_to_pattern_and_replacement
                   (gets_inlined : forall t, value (type.base t) -> bool)
                   (should_do_again : bool) evm
                   (invalid : forall A B, A -> B)
                   {t} (lhs rhs : @expr.expr base_type ident (fun _ => positive) t)
                   (side_conditions : (positive -> bool) -> list bool)
          : { p : pattern (pattern.type.relax t) & @with_unif_rewrite_ruleTP_gen' _ p should_do_again true true evm }
          := let (p, unif_data_lhs) := @pattern_of_expr evm (fun _ => invalid _ _) t lhs in
             existT
               _
               p
               (pattern.type.subst_default_relax
                  (fun t'
                   => with_unification_resultT'
                        pident_arg_types p evm
                        (option (UnderLets (expr_maybe_do_again should_do_again t'))))
                  (lam_unification_resultT'
                     (fun unif_data_new
                      => let '(value_map, side_conditions) := pair'_unification_resultT' unif_data_lhs unif_data_new (PositiveMap.empty _, side_conditions) in
                         let side_conditions := side_conditions (lookup_expr_gets_inlined (invalid _ _) gets_inlined value_map) in
                         let start_i := Pos.succ (PositiveMap.fold (fun k _ max => Pos.max k max) value_map 1%positive) in
                         let replacement := expr_pos_to_expr_value (fun _ => invalid _ _) rhs value_map start_i in
                         let replacement := expr_value_to_rewrite_rule_replacement should_do_again replacement in
                         if fold_left andb (List.rev side_conditions) true
                         then Some replacement
                         else None))).

        Definition expr_to_pattern_and_replacement_unfolded gets_inlined should_do_again evm invalid {t} lhs rhs side_conditions
          := Eval cbv beta iota delta [expr_to_pattern_and_replacement lookup_expr_gets_inlined pattern_of_expr lam_unification_resultT' Pos.succ pair'_unification_resultT' PositiveMap.empty PositiveMap.fold Pos.max expr_pos_to_expr_value   fold_left List.rev List.app value PositiveMap.add PositiveMap.xfoldi Pos.compare Pos.compare_cont FMapPositive.append projT1 projT2 PositiveMap.find Base_value   lam_type_of_list fold_right list_rect pattern.type.relax pattern.type.subst_default pattern.type.subst_default_relax pattern.type.unsubst_default_relax option_map unification_resultT' with_unification_resultT' with_unif_rewrite_ruleTP_gen']
            in @expr_to_pattern_and_replacement gets_inlined should_do_again evm invalid t lhs rhs side_conditions.

        Definition partial_lam_unif_rewrite_ruleTP_gen_unfolded should_do_again {t} p
          := Eval cbv beta iota delta [partial_lam_unif_rewrite_ruleTP_gen pattern.collect_vars pattern.type.lam_forall_vars partial_lam_unification_resultT pattern.type.collect_vars pattern.base.collect_vars PositiveSet.union PositiveSet.add PositiveSet.empty pattern.type.lam_forall_vars_gen List.rev PositiveSet.elements PositiveSet.xelements PositiveSet.rev PositiveSet.rev_append List.app orb fold_right PositiveMap.add PositiveMap.empty]
            in @partial_lam_unif_rewrite_ruleTP_gen base ident var pident pident_arg_types value t p should_do_again true true.
      End with_var.

       
      Ltac2 binder_name_or_fresh_default (b : binder) (avoid : constr) (default_base : ident) : ident
        := match Constr.Binder.name b with
           | Some n => n
           | None => Fresh.fresh (Fresh.Free.union (Fresh.Free.of_goal ()) (Fresh.Free.of_constr avoid)) default_base
           end.

      Ltac2 Type exn ::= [ Cannot_eliminate_functional_dependencies (constr) ].
      Ltac2 strip_functional_dependency (term : constr) : constr :=
        lazy_match! term with
        | fun _ => ?p => p
        | _ => Control.zero (Cannot_eliminate_functional_dependencies term)
        end.
      Ltac2 rec refine_reify_under_forall_types' (base_type : constr) (base_type_interp : constr) (ty_ctx : constr) (cur_i : constr) (lem : constr) (cont : constr   -> constr   -> constr   -> unit) : unit :=
        let debug_Constr_check := let dummy_var := 'I in
                                  fun e => (printf "Checking: %t" e; let v := Reify.debug_Constr_check "refine_reify_under_forall_types'" (fun _ _ => Message.of_exn) dummy_var [] [] e in printf "Checked"; v) in
        let default () := cont ty_ctx cur_i lem in
        match Constr.Unsafe.kind lem with
        | Constr.Unsafe.Cast lem _ _ => refine_reify_under_forall_types' base_type base_type_interp ty_ctx cur_i lem cont
        | Constr.Unsafe.Prod b p
          => let n := binder_name_or_fresh_default b lem @T in
             if Constr.is_sort (Constr.Binder.type b)
             then
               Control.refine
                 (fun ()
                  => strip_functional_dependency
                       (Constr.in_context
                          n base_type
                          (fun ()
                           => let rt := mkVar n in
                              printf "1";
                              let ty_ctx := debug_Constr_check (mkApp 'PositiveMap.add [base_type; cur_i; rt; ty_ctx]) in
                              printf "2";
                              let t := debug_Constr_check (mkApp base_type_interp [mkApp '@pattern.base.lookup_default ['_; cur_i; ty_ctx] ]) in
                              printf "3";
                              let p := debug_Constr_check (Constr.Unsafe.substnl [t] 0 p) in
                              printf "3";
                              let cur_i := Std.eval_vm None (mkApp 'Pos.succ [cur_i]) in
                              printf "4";
                              refine_reify_under_forall_types' base_type base_type_interp ty_ctx cur_i p cont)))
             else
               default ()
        | _ => default ()
        end.

      Ltac2 refine_reify_under_forall_types (base_type : constr) (base_type_interp : constr) (lem : constr) (cont : constr   -> constr   -> constr   -> unit) : unit :=
        refine_reify_under_forall_types' base_type base_type_interp '(@PositiveMap.empty $base_type) '(1%positive) lem cont.
      Ltac2 reify_under_forall_types (base_type : constr) (base_type_interp : constr) (lem : constr) (cont : constr   -> constr   -> constr   -> constr) : constr :=
        '(ltac2:(refine_reify_under_forall_types base_type base_type_interp lem (fun ty_ctx cur_i lem => Control.refine (fun () => cont ty_ctx cur_i lem)))).

      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
       Ltac reify_under_forall_types base_type base_type_interp lem cont :=
        let f := ltac2:(base_type base_type_interp lem cont
                        |- let cont ty_ctx cur_i lem
                             := Ltac1.apply cont [Ltac1.of_constr ty_ctx; Ltac1.of_constr cur_i; Ltac1.of_constr lem] Ltac1.run in
                           refine_reify_under_forall_types (Ltac1.get_to_constr "base_type" base_type) (Ltac1.get_to_constr "base_type_interp" base_type_interp) (Ltac1.get_to_constr "lem" lem) cont) in
        constr:(ltac:(f base_type base_type_interp lem ltac:(fun ty_ctx cur_i lem => let v := cont ty_ctx cur_i lem in refine v))).

      Ltac prop_to_bool H := eval cbv [decb] in (decb H).

      Ltac push_side_conditions H side_conditions :=
        constr:(H :: side_conditions).

      Ltac equation_to_parts' lem side_conditions :=
        lazymatch lem with
        | ?H -> ?P
          => let __ := lazymatch type of H with
                       | Prop => constr:(I)
                       | ?T => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-Prop non-dependent hypothesis of type" H ":" T "when reifying a lemma of type" lem)
                       end in
             let H := prop_to_bool H in
             let side_conditions := push_side_conditions H side_conditions in
             equation_to_parts' P side_conditions
        | forall x : ?T, ?P
          => let P' := fresh in
             constr:(
               fun x : T
               => match P return _ with
                  | P'
                    => ltac:(let P := (eval cbv delta [P'] in P') in
                             clear P';
                             let res := equation_to_parts' P side_conditions in
                             exact res)
                  end)
        | @eq ?T ?A ?B
          => constr:((@eq T A B, side_conditions))
        | ?T => constr_fail_with ltac:(fun _ => fail 1 "Invalid type of equation:" T)
        end.
      Ltac equation_to_parts lem :=
        equation_to_parts' lem (@nil bool).

      Ltac preadjust_pattern_type_variables pat :=
        let pat := (eval cbv [pattern.type.relax pattern.type.subst_default pattern.type.subst_default_relax pattern.type.unsubst_default_relax] in pat) in
        let pat := (eval cbn [pattern.base.relax pattern.base.subst_default pattern.base.subst_default_relax pattern.base.unsubst_default_relax] in pat) in
        pat.

      Ltac adjust_pattern_type_variables' pat :=
        lazymatch pat with
        | context[@pattern.base.relax ?base (pattern.base.lookup_default ?p ?evm')]
          => let t := constr:(@pattern.base.relax base (pattern.base.lookup_default p evm')) in
             let T := fresh in
             let pat :=
                 lazymatch (eval pattern t in pat) with
                 | ?pat _
                   => let P := match type of pat with forall x, @?P x => P end in
                      lazymatch pat with
                      | fun T => ?pat
                        => constr:(match pattern.base.type.var p as T return P T with
                                   | T => pat
                                   end)
                      end
                 end in
             adjust_pattern_type_variables' pat
        | ?pat => pat
        end.

      Ltac adjust_pattern_type_variables_internal pat :=
        let pat := preadjust_pattern_type_variables pat in
        adjust_pattern_type_variables' pat.
      Ltac adjust_pattern_type_variables pat :=
        constr:(ltac:(let v := adjust_pattern_type_variables_internal pat in refine v)).

      Ltac walk_term_under_binders_fail_invalid invalid term fv :=
        lazymatch fv with
        | context[invalid _ _ ?x]
          => fail 0 "Invalid (in" term "): Invalid:" x
        | context[invalid]
          => lazymatch fv with
             | ?f ?x => walk_term_under_binders_fail_invalid invalid term f;
                        walk_term_under_binders_fail_invalid invalid term x
             | fun (x : ?T) => @?f x
               => let __ :=
                      constr:(
                        fun x : T
                        => ltac:(let f := (eval cbv beta in (f x)) in
                                 walk_term_under_binders_fail_invalid invalid term f;
                                 exact I)) in
                  idtac
             | context[invalid _ ?x]
               => fail 0 "Invalid (second arg) (in" term "): Invalid:" x
             end
        | _ => idtac
        end.

      Ltac strip_invalid_or_fail term :=
        lazymatch term with
        | fun _ => ?f => f
        | fun invalid : ?T => ?f
          => let f' := fresh in
             constr:(fun invalid : T
                     => match f return _ with
                        | f'
                          => ltac:(let f := (eval cbv [f'] in f') in
                                   walk_term_under_binders_fail_invalid invalid term f;
                                   fail 0 "Invalid (unknown subterm):" term)
                        end)
        end.

      Definition pattern_base_subst_default_relax' {base} t evm P
        := @pattern.base.subst_default_relax base P t evm.
      Definition pattern_base_unsubst_default_relax' {base} t evm P
        := @pattern.base.unsubst_default_relax base P t evm.

      Ltac change_pattern_base_subst_default_relax_internal term :=
        lazymatch (eval pattern (@pattern.base.subst_default_relax), (@pattern.base.unsubst_default_relax) in term) with
        | ?f _ _
          => let base := fresh "base" in
             let P := fresh "P" in
             let t := fresh "t" in
             let evm := fresh "evm" in
             (eval cbv beta in (f (fun base P t evm => @pattern_base_subst_default_relax' base t evm P) (fun base P t evm => @pattern_base_unsubst_default_relax' base t evm P)))
        end.
      Ltac change_pattern_base_subst_default_relax term :=
        constr:(ltac:(let v := change_pattern_base_subst_default_relax_internal term in refine v)).

      Ltac adjust_lookup_default_internal rewr :=
        lazymatch (eval pattern (@pattern.base.lookup_default) in rewr) with
        | ?rewr _
          => let base := fresh "base" in
             let p := fresh "p" in
             let evm := fresh "evm" in
             (eval cbv beta in (rewr (fun base p evm => @pattern.base.subst_default base (pattern.base.type.var p) evm)))
        end.
      Ltac adjust_lookup_default rewr :=
        constr:(ltac:(let v := adjust_lookup_default_internal rewr in refine v)).

      Ltac replace_evar_map_internal evm rewr :=
        let evm' := match rewr with
                    | context[pattern.base.lookup_default _ ?evm']
                      => let __ := match goal with _ => tryif constr_eq evm evm' then fail else idtac end in
                         evm'
                    | context[pattern.base.subst_default _ ?evm']
                      => let __ := match goal with _ => tryif constr_eq evm evm' then fail else idtac end in
                         evm'
                    | _ => tt
                    end in
        lazymatch evm' with
        | tt => rewr
        | _
          => let rewr := lazymatch (eval pattern evm' in rewr) with
                         | ?rewr _ => (eval cbv beta in (rewr evm))
                         end in
             replace_evar_map_internal evm rewr
        end.
      Ltac replace_evar_map evm rewr :=
        constr:(ltac:(let v := replace_evar_map_internal evm rewr in refine v)).

      Ltac adjust_type_variables_internal rewr :=
        lazymatch rewr with
        | context[@pattern.base.subst_default ?base (pattern.base.relax ?t) ?evm'']
          => let t' := constr:(@pattern.base.subst_default base (pattern.base.relax t) evm'') in
             let rewr :=
                 lazymatch (eval pattern
                                 t',
                            (@pattern_base_subst_default_relax' base t evm''),
                            (@pattern_base_unsubst_default_relax' base t evm'')
                             in rewr)
                 with
                 | ?rewr _ _ _
                   => (eval cbv beta in (rewr t (fun P x => x) (fun P x => x)))
                 end in
             adjust_type_variables_internal rewr
        | _ => rewr
        end.
      Ltac adjust_type_variables rewr :=
        constr:(ltac:(let v := adjust_type_variables_internal rewr in refine v)).

      Ltac replace_type_try_transport_internal term :=
        lazymatch term with
        | context[@type.try_transport ?base_type ?try_make_transport_base_type_cps ?P ?t ?t]
          => let v := constr:(@type.try_transport base_type try_make_transport_base_type_cps P t t) in
             let term := lazymatch (eval pattern v in term) with
                         | ?term _ => (eval cbv beta in (term (@Some _)))
                         end in
             replace_type_try_transport_internal term
        | _ => term
        end.
      Ltac replace_type_try_transport term :=
        constr:(ltac:(let v := replace_type_try_transport_internal term in refine v)).

      Ltac under_binders payload term cont ctx :=
        lazymatch term with
        | (fun x : ?T => ?f)
          => let ctx' := fresh in
             let f' := fresh in
             let payload' := fresh in  
             constr:(match payload return _ with
                     | payload'
                       => fun x : T
                          => match f, dyncons x ctx return _ with
                             | f', ctx'
                               => ltac:(let ctx := (eval cbv delta [ctx'] in ctx') in
                                        let f := (eval cbv delta [f'] in f') in
                                        let payload := (eval cbv delta [payload'] in payload') in
                                        clear f' ctx' payload';
                                        let res := under_binders payload f cont ctx in
                                        exact res)
                             end
                     end)
        | ?term => cont payload ctx term
        end.
      Ltac substitute_with term x y :=
        lazymatch (eval pattern y in term) with
        | (fun z => ?term) _ => constr:(match x return _ with z => term end)
        end.
      Ltac substitute_beq_with base_interp_beq only_eliminate_in_ctx full_ctx term beq x :=
        let is_good y :=
            lazymatch full_ctx with
            | context[dyncons y _] => fail
            | _ => is_var y;
                   lazymatch only_eliminate_in_ctx with
                   | context[y] => idtac
                   end
            end in
        let y := match term with
                 | context term' [beq x ?y]
                   => let __ := is_good y in
                      constr:(Some (beq x y))
                 | context term' [@base.interp_beq ?base ?base_interp ?base_interp_beq ?t x ?y]
                   => let __ := is_good y in
                      constr:(Some (@base.interp_beq base base_interp base_interp_beq t x y))
                 | context term' [base_interp_beq ?t x ?y]
                   => let __ := is_good y in
                      constr:(Some (base_interp_beq t x y))
                 | context term' [base_interp_beq ?t1 ?t2 x ?y]  
                   => let __ := is_good y in
                      constr:(Some (base_interp_beq t1 t2 x y))
                 | _ => constr:(@None unit)
                 end in
        lazymatch y with
        | Some (?beq x ?y)
          => lazymatch term with
             | context term'[beq x y]
               => let term := context term'[true] in
                  substitute_with term x y
             end
        | None => term
        end.
      Ltac remove_andb_true term :=
        let term := lazymatch (eval pattern andb, (andb true) in term) with
                    | ?f _ _ => (eval cbn [andb] in (f (fun x y => andb y x) (fun b => b)))
                    end in
        let term := lazymatch (eval pattern andb, (andb true) in term) with
                    | ?f _ _ => (eval cbn [andb] in (f (fun x y => andb y x) (fun b => b)))
                    end in
        term.
      Ltac adjust_if_negb term :=
        lazymatch term with
        | context term'[if negb ?x then ?a else ?b]
          => let term := context term'[if x then b else a] in
             adjust_if_negb term
        | _ => term
        end.
      Ltac substitute_bool_eqb term :=
        lazymatch term with
        | context term'[Bool.eqb ?x true]
          => let term := context term'[x] in
             substitute_bool_eqb term
        | context term'[Bool.eqb ?x false]
          => let term := context term'[negb x] in
             substitute_bool_eqb term
        | context term'[Bool.eqb true ?x]
          => let term := context term'[x] in
             substitute_bool_eqb term
        | context term'[Bool.eqb false ?x]
          => let term := context term'[negb x] in
             substitute_bool_eqb term
        | _ => term
        end.

      Ltac substitute_beq base_interp_beq only_eliminate_in_ctx full_ctx ctx term :=
        let base_interp_beq_head := head base_interp_beq in
        lazymatch ctx with
        | dynnil
          => let term := (eval cbv [base.interp_beq base_interp_beq_head] in term) in
             let term := substitute_bool_eqb term in
             let term := remove_andb_true term in
             let term := adjust_if_negb term in
             term
        | dyncons ?v ?ctx
          => let term := substitute_beq_with base_interp_beq only_eliminate_in_ctx full_ctx term Z.eqb v in
             let term := match constr:(Set) with
                         | _ => let T := type of v in
                                let beq := (eval cbv beta delta [Reflect.decb_rel] in (Reflect.decb_rel (@eq T))) in
                                substitute_beq_with base_interp_beq only_eliminate_in_ctx full_ctx term beq v
                         | _ => term
                         end in
             substitute_beq base_interp_beq only_eliminate_in_ctx full_ctx ctx term
        end.

      Ltac deep_substitute_beq base_interp_beq only_eliminate_in_ctx term :=
        lazymatch term with
        | context term'[@Build_rewrite_rule_data ?base ?ident ?var ?pident ?pident_arg_types ?t ?p ?sda ?wo ?ul ?subterm]
          => let subterm := under_binders only_eliminate_in_ctx subterm ltac:(fun only_eliminate_in_ctx ctx term => substitute_beq base_interp_beq only_eliminate_in_ctx ctx ctx term) dynnil in
             let term := context term'[@Build_rewrite_rule_data base ident var pident pident_arg_types t p sda wo ul subterm] in
             term
        end.

      Ltac clean_beq_internal base_interp_beq only_eliminate_in_ctx term :=
        let base_interp_beq_head := head base_interp_beq in
        let term := (eval cbn [Prod.prod_beq] in term) in
        let term := (eval cbv [ident.literal] in term) in
        let term := deep_substitute_beq base_interp_beq only_eliminate_in_ctx term in
        let term := (eval cbv [base.interp_beq base_interp_beq_head] in term) in
        let term := remove_andb_true term in
        term.
      Ltac clean_beq base_interp_beq only_eliminate_in_ctx term :=
        constr:(ltac:(let v := clean_beq_internal base_interp_beq only_eliminate_in_ctx term in refine v)).

      Ltac adjust_side_conditions_for_gets_inlined' value_ctx side_conditions lookup_gets_inlined :=
        lazymatch side_conditions with
        | context sc[ident.gets_inlined _ ?x]
          => lazymatch value_ctx with
             | context[expr.var_context.cons x ?p _]
               => let rep := constr:(lookup_gets_inlined p) in
                  let side_conditions := context sc[rep] in
                  adjust_side_conditions_for_gets_inlined' value_ctx side_conditions lookup_gets_inlined
             | _ => constr_fail_with ltac:(fun _ => fail 1 "Could not find an expression corresponding to" x "in context" value_ctx)
             end
        | _ => side_conditions
        end.

      Ltac adjust_side_conditions_for_gets_inlined value_ctx side_conditions :=
        let lookup_gets_inlined := fresh in
        constr:(fun lookup_gets_inlined : positive -> bool
                => ltac:(let v := adjust_side_conditions_for_gets_inlined' value_ctx side_conditions lookup_gets_inlined in
                         exact v)).

      Ltac reify_to_pattern_and_replacement_in_context base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota type_ctx var gets_inlined should_do_again cur_i term value_ctx :=
        let base_type := constr:(base.type base) in
        let reify_base_type := ltac:(Compilers.base.reify base reify_base) in
        let base_interp_head := head base_interp in
        let t := fresh "t" in
        let p := fresh "p" in
        let reify_rec_gen type_ctx := reify_to_pattern_and_replacement_in_context base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota type_ctx var gets_inlined should_do_again in
        let var_pos := constr:(fun _ : type base_type => positive) in
        let value := constr:(@value base_type ident var) in
        let cexpr_to_pattern_and_replacement_unfolded := constr:(@expr_to_pattern_and_replacement_unfolded base try_make_transport_base_cps ident var pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident (reflect_ident_iota var) gets_inlined should_do_again type_ctx) in
        let cpartial_lam_unif_rewrite_ruleTP_gen := constr:(@partial_lam_unif_rewrite_ruleTP_gen_unfolded base ident var pident pident_arg_types should_do_again) in
        let cwith_unif_rewrite_ruleTP_gen := constr:(fun t p => @with_unif_rewrite_ruleTP_gen base ident var pident pident_arg_types value t p should_do_again true true) in
        lazymatch term with
        | (fun x : ?T => ?f)
          => let rT := Compilers.type.reify reify_base_type base_type T in
             let not_x1 := fresh in
             let not_x2 := fresh in
             let next_i := (eval vm_compute in (Pos.succ cur_i)) in
             let type_ctx' := fresh in  
             let rf0 :=
                 constr:(
                   match type_ctx return _ with
                   | type_ctx'
                     => fun (x : T)
                        => match f, @expr.var_context.cons base_type var_pos T rT x cur_i value_ctx return _ with  
                           | not_x1, not_x2
                             => ltac:(
                                  let f := (eval cbv delta [not_x1] in not_x1) in
                                  let value_ctx := (eval cbv delta [not_x2] in not_x2) in
                                  let type_ctx := (eval cbv delta [type_ctx'] in type_ctx') in
                                  clear not_x1 not_x2 type_ctx';
                                  let rf := reify_rec_gen type_ctx next_i f value_ctx in
                                  exact rf)
                           end
                   end) in
             lazymatch rf0 with
             | (fun _ => ?f) => f
             | _
               => constr_fail_with ltac:(fun _ => fail 1 "Failure to eliminate functional dependencies of" rf0)
             end
        | (@eq ?T ?A ?B, ?side_conditions)
          => let rA := expr.reify_in_context base_type ident reify_base_type reify_ident var_pos A value_ctx tt in
             let rB := expr.reify_in_context base_type ident reify_base_type reify_ident var_pos B value_ctx tt in
             let side_conditions := adjust_side_conditions_for_gets_inlined value_ctx side_conditions in
             let invalid := fresh "invalid" in
             let res := constr:(fun invalid => cexpr_to_pattern_and_replacement_unfolded invalid _ rA rB side_conditions) in
             let res := (eval cbv [expr_to_pattern_and_replacement_unfolded pident_arg_types pident_of_typed_ident pident_type_of_list_arg_types_beq pident_arg_types_of_typed_ident  ] in res) in
             let res := (eval cbn [fst snd andb pattern.base.relax pattern.base.subst_default pattern.base.subst_default_relax] in res) in
             let res := change_pattern_base_subst_default_relax res in
             let p := (eval cbv [projT1] in (fun invalid => projT1 (res invalid))) in
             let p := strip_invalid_or_fail p in
             let p := adjust_pattern_type_variables p in
             let res := (eval cbv [projT2] in (fun invalid => projT2 (res invalid))) in
             let evm' := fresh "evm" in
             let res' := fresh in
             let res :=
                 constr:(
                   fun invalid (evm' : EvarMap_at base)
                   => match res invalid return _ with
                      | res'
                        => ltac:(let res := (eval cbv beta delta [res'] in res') in
                                 clear res';
                                 let res := adjust_lookup_default res in
                                 let res := adjust_type_variables res in
                                 let res := replace_evar_map evm' res in
                                 let res := replace_type_try_transport res in
                                 exact res)
                      end) in
             let res := (eval cbv [UnderLets.map UnderLets.flat_map reify_expr_beta_iota reflect_expr_beta_iota reify_to_UnderLets] in res) in
             let res := (eval cbn [reify reflect UnderLets.of_expr UnderLets.to_expr UnderLets.splice value' Base_value invert_Literal invert_ident_Literal splice_under_lets_with_value] in res) in
             let res := strip_invalid_or_fail res in
              
             let res := (eval cbv [partial_lam_unif_rewrite_ruleTP_gen_unfolded] in
                            (existT
                               (cwith_unif_rewrite_ruleTP_gen _)
                               p
                               (cpartial_lam_unif_rewrite_ruleTP_gen _ p res))) in
              
             let res := (eval cbn [pattern.base.subst_default pattern.base.lookup_default PositiveMap.find type.interp base.interp base_interp_head] in res) in
             let res := (eval cbv [projT1 projT2] in
                            (existT
                               (@rewrite_ruleTP base ident var pident pident_arg_types)
                               {| pattern.pattern_of_anypattern := projT1 res |}
                               {| rew_replacement := projT2 res |})) in
             let res := clean_beq base_interp_beq value_ctx res in
             res
        end.

      Ltac reify base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var gets_inlined should_do_again lem :=
        let base_type := constr:(Compilers.base.type base) in
        let base_type_interp := constr:(@Compilers.base.interp base base_interp) in
        reify_under_forall_types
          base_type
          base_type_interp
          lem
          ltac:(
          fun ty_ctx cur_i lem
          => let lem := equation_to_parts lem in
             let res := reify_to_pattern_and_replacement_in_context base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota ty_ctx var gets_inlined should_do_again constr:(1%positive) lem (@expr.var_context.nil (base.type base) (fun _ => positive)) in
             res).

      Ltac Reify base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota gets_inlined should_do_again lem :=
        let var := fresh "var" in
        constr:(fun var : Compilers.type.type (Compilers.base.type base) -> Type
                => ltac:(let res := reify base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var (gets_inlined var) should_do_again lem in
                         exact res)).

       
      Ltac reify_list base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var gets_inlined lems :=
        let reify' := reify base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var gets_inlined in
        let reify_list_rec := reify_list base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var gets_inlined in
        lazymatch (eval hnf in lems) with
        | (?b, ?lem) :: ?lems
          => let rlem := reify' b lem in
             let rlems := reify_list_rec lems in
             constr:(rlem :: rlems)
        | nil => constr:(@nil (@rewrite_ruleT base ident var pident pident_arg_types))
        | _
          => let List_map := (eval cbv delta [List.map] in (@List.map)) in
             let lems := (eval cbv beta iota in
                             (List_map _ _ (fun p : Prop => (false, p)) lems)) in
             reify_list_rec lems
        end.

      Ltac Reify_list base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota gets_inlined lems :=
        let var := fresh "var" in
        constr:(fun var : Compilers.type.type (Compilers.base.type base) -> Type
                => ltac:(let res := reify_list base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var (gets_inlined var) lems in
                         exact res)).
    End Reify.

    Module Make.
      Export Rewriter.Compilers.RewriteRules.Make.
      Import pattern.ident.GoalType.

      Ltac build_pident_pair exprExtraInfo pkg :=
        let v := (eval vm_compute in
                     (fun A B => @of_typed_ident_of pkg _ (@ident.ident_pair _ _ _ (@Classes.buildIdent _ exprExtraInfo) A B))) in
        let h := lazymatch v with fun A B => ?f _ _ => f end in
        h.
      Section make_rewrite_rules.
        Import Compile.
        Section expanded.
          Context {base : Type}.
          Local Notation base_type := (base.type base).
          Local Notation type := (type.type base_type).
          Context {base_interp : base -> Type}
                  {ident : type -> Type}
                  {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}
                  {BuildIdentT : @ident.BuildIdentT base base_interp ident}
                  {baseDefault : @DefaultValue.type.base.DefaultT base base_interp}
                  {pkg : @package base ident}
                  {var : type -> Type}.
          Local Notation expr := (@expr.expr base_type ident var).
          Local Notation value := (@value base_type ident var).
          Local Notation pattern := (@pattern.pattern base pattern_ident).
          Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
          Local Notation pbase_type := (pattern.base.type base).
          Local Notation ptype := (type.type pbase_type).
          Let type_base {base} (t : base.type base) : type.type (base.type base) := type.base t.
          Let ptype_base {base} (t : pattern.base.type base) : type.type (pattern.base.type base) := type.base t.
          Let type_base' (t : base) : base_type := base.type.type_base t.
          Let ptype_base' (t : base) : pbase_type := pattern.base.type.type_base t.
          Let type_base'' (t : base) : type := type.base (base.type.type_base t).
          Let ptype_base'' (t : base) : ptype := type.base (pattern.base.type.type_base t).
          Coercion ptype_base'' : base >-> ptype.
          Coercion type_base : base_type >-> type.
          Coercion ptype_base : pbase_type >-> ptype.
          Local Notation collect_vars := (@pattern.collect_vars base pattern_ident).
          Local Notation with_unification_resultT' := (@with_unification_resultT' base pattern_ident (@arg_types) value).
          Local Notation with_unification_resultT := (@with_unification_resultT base pattern_ident (@arg_types) value).
          Local Notation under_with_unification_resultT' := (@under_with_unification_resultT' base pattern_ident (@arg_types) value).
          Local Notation under_with_unification_resultT := (@under_with_unification_resultT base pattern_ident (@arg_types) value).
          Local Notation rewrite_ruleTP := (@rewrite_ruleTP base ident var pattern_ident (@arg_types)).
          Local Notation rewrite_ruleT := (@rewrite_ruleT base ident var pattern_ident (@arg_types)).
          Local Notation rewrite_rule_data := (@rewrite_rule_data base ident var pattern_ident (@arg_types)).

          Definition make_base_Literal_pattern_folded (t : base) : pattern t
            :=  
              pattern.Ident (of_typed_ident_unfolded (type_base'' t) (ident.ident_Literal (t:=t) (DefaultValue.type.base.default (t:=type_base' t)))).

          Context (pident_pair : forall A B : pbase_type, pattern_ident (A -> B -> A * B)%ptype).

          Fixpoint make_Literal_pattern (t : pbase_type) : option (pattern t)
            := match t return option (pattern t) with
               | pattern.base.type.var _ => None
               | pattern.base.type.type_base t => Some (make_base_Literal_pattern_folded t)
               | pattern.base.type.prod A B
                 => (a <- make_Literal_pattern A;
                       b <- make_Literal_pattern B;
                       Some ((#(pident_pair _ _) @ a @ b)%pattern))
               | pattern.base.type.unit => None
               | pattern.base.type.list A => None
               | pattern.base.type.option A => None
               end%option.

          Fixpoint make_interp_rewrite_pattern {t}
            : pattern t -> option (pattern (type.final_codomain t))
            := match t return pattern t -> option (pattern (type.final_codomain t)) with
               | type.base t
                 => fun p => Some p
               | type.arrow (type.base s) d
                 => fun p => (x <- make_Literal_pattern s; @make_interp_rewrite_pattern d (pattern.App p x))%option
               | type.arrow _ _ => fun _ => None
               end.

          Lemma collect_vars_literal_empty {t}
            : match make_Literal_pattern t with
              | Some p => collect_vars p = PositiveSet.empty /\ pattern.base.collect_vars t = PositiveSet.empty
              | None => True
              end.
Admitted.

          Context (cast_Literal_base_pattern_interp
                   : forall (evm : EvarMap) (t : base),
                      unification_resultT' (var:=var) (@arg_types) (make_base_Literal_pattern_folded t) evm
                      -> base.interp base_interp (pattern.base.subst_default (ptype_base' t) evm)).

          Fixpoint make_Literal_pattern_interp_helper {t evm T}
                   {struct t}
            : match make_Literal_pattern t with
              | Some x
                => (base.interp base_interp (pattern.base.subst_default t evm) -> T)
                   -> with_unification_resultT' x evm T
              | None => True
              end.
          Proof.
            refine match t return match make_Literal_pattern t with
                                  | Some x
                                    => (base.interp base_interp (pattern.base.subst_default t evm) -> T)
                                       -> with_unification_resultT' x evm T
                                  | None => True
                                  end
                   with
                   | pattern.base.type.var _
                   | pattern.base.type.list _
                   | pattern.base.type.option _
                   | pattern.base.type.unit
                     => I
                   | pattern.base.type.type_base t
                     => fun f => lam_unification_resultT' _ (fun x => f (cast_Literal_base_pattern_interp _ _ x))
                   | pattern.base.type.prod A B
                     => let recA := @make_Literal_pattern_interp_helper
                                      A evm
                                      (match make_Literal_pattern A, make_Literal_pattern B return Type with
                                       | Some a, Some b => _
                                       | _, _ => unit
                                       end) in
                        let recB := @make_Literal_pattern_interp_helper
                                      B evm
                                      (match make_Literal_pattern A, make_Literal_pattern B return Type with
                                       | Some a, Some b => _
                                       | _, _ => unit
                                       end) in
                        _
                   end;
              clearbody recA recB;
              cbn [make_Literal_pattern] in *.
            destruct (make_Literal_pattern A) as [a|], (make_Literal_pattern B) as [b|]; try exact I; cbn [Option.bind with_unification_resultT'].
            refine (fun f
                    => lam_type_of_list
                         (fun _ => recA (fun a' => recB (fun b' => f (a', b'))))).
          Defined.

           
          Definition strip_collect_vars
                     {s : pbase_type} {d : ptype}
                     {p : pattern (type.base s -> d)%ptype}
                     (p_res : pattern.type.forall_vars
                                (collect_vars p)
                                (fun evm =>
                                   with_unification_resultT'
                                     p evm
                                     (type.interp (base.interp base_interp) (pattern.type.subst_default (type.base s -> d)%ptype evm))))
            : forall (rec : forall x : pattern (type.base s),
                         pattern.type.forall_vars (PositiveSet.union (collect_vars x) (collect_vars p))
                                                  (fun evm =>
                                                     with_unification_resultT'
                                                       p evm
                                                       (with_unification_resultT'
                                                          x evm
                                                          (type.interp (base.interp base_interp) (pattern.type.subst_default d evm))))
                         -> match make_interp_rewrite_pattern (p @ x) with
                            | Some p' => @rewrite_rule_data _ p'
                            | None => True
                            end),
              match (x <- make_Literal_pattern s;
                       make_interp_rewrite_pattern (p @ x))%option with
              | Some p' => @rewrite_rule_data _ p'
              | None => True
              end.
          Proof.
            intro rec_call.
            pose proof (@collect_vars_literal_empty s) as H.
            pose proof (@make_Literal_pattern_interp_helper s) as F.
            destruct (make_Literal_pattern s) as [x|]; [ | exact I ]; cbn [Option.bind].
            cbv [ptype_base] in *.
            refine (rec_call x _); clear rec_call.
            destruct (pattern.collect_vars x); [ | exfalso; clear -H; abstract (destruct H as [H _]; cbv in H; discriminate) ].
            refine (pattern.type.under_forall_vars (fun evm => under_with_unification_resultT' (F _ _)) p_res).
          Defined.

          Fixpoint make_interp_rewrite'_helper {t}
            : forall (p : pattern t)
                     (base_rewrite : with_unification_resultT p (type.interp (base.interp base_interp)))
                     (p' := make_interp_rewrite_pattern p),
              match p' return Type with
              | Some p' => rewrite_ruleTP {| pattern.pattern_of_anypattern := p' |}
              | None => True
              end
            := match t return (forall (p : pattern t)
                                      (base_rewrite : with_unification_resultT p (type.interp (base.interp base_interp)))
                                      (p' := make_interp_rewrite_pattern p),
                                  match p' return Type with
                                  | Some p' => rewrite_ruleTP {| pattern.pattern_of_anypattern := p' |}
                                  | None => True
                                  end)
               with
               | type.base t
                 => fun p base_rewrite
                    => {| rew_should_do_again := false;
                          rew_with_opt := false;
                          rew_under_lets := false;
                          rew_replacement
                          := under_with_unification_resultT
                               (fun evm v => ident.smart_Literal v)
                               base_rewrite |}
               | type.arrow (type.base s) d
                 => fun p base_rewrite
                    => let rec_call
                           := fun x => @make_interp_rewrite'_helper d (p @ x)%pattern in
                       strip_collect_vars base_rewrite rec_call
               | type.arrow _ _
                 => fun _ _ => I
               end.

          Definition make_interp_rewrite' {t} (idc : ident t)
                     (pidc := pattern.Ident (@of_typed_ident _ idc))
                     (val : with_unification_resultT pidc (type.interp (base.interp base_interp)))
            : option rewrite_ruleT
            := match make_interp_rewrite_pattern pidc as p
                     return match p return Type with
                            | Some p' => rewrite_ruleTP {| pattern.pattern_of_anypattern := p' |}
                            | None => True
                            end
                            -> option rewrite_ruleT
               with
               | Some p'
                 => fun r
                    => Some (existT _ {| pattern.pattern_of_anypattern := p' |} r)
               | None => fun _ => None
               end (make_interp_rewrite'_helper pidc val).

          Definition make_default_with_unification_resultT {t vs ls} (v : type.interp (base.interp base_interp) t)
            : pattern.type.forall_vars
                vs
                (fun evm =>
                   fold_right (fun a K : Type => a -> K)
                              (type.interp (base.interp base_interp) (pattern.type.subst_default (pattern.type.relax t) evm))
                              ls)
            := pattern.type.lam_forall_vars
                 (fun evm
                  => list_rect
                       (fun ls => fold_right (fun a K => a -> K) _ ls)
                       (pattern.type.subst_default_relax (t:=t) _ v)
                       (fun x xs rec _ => rec)
                       _).

          Definition make_interp_rewrite'' {t} (idc : ident t) : option rewrite_ruleT
            := @make_interp_rewrite'
                 t idc (make_default_with_unification_resultT (ident_interp _ idc)).

          Definition interp_rewrite_rules_folded' : list _
            := Option.List.map
                 (fun tidc => make_interp_rewrite'' (PrimitiveSigma.Primitive.projT2 tidc))
                 simple_idents.
        End expanded.

        Section bundled.
          Context {exprInfo : Classes.ExprInfoT}
                  {exprExtraInfo : Classes.ExprExtraInfoT}
                  {pkg : @package Classes.base Classes.ident}.

          Definition interp_rewrite_rules_folded {var} pident_pair cast_Literal_base_pattern_interp : list _
            := @interp_rewrite_rules_folded' _ _ _ Classes.ident_interp _ _ _ var pident_pair cast_Literal_base_pattern_interp.
        End bundled.
      End make_rewrite_rules.

      Ltac build_interp_rewrite_rules exprInfo exprExtraInfo pkg :=
        let exprInfo := (eval hnf in exprInfo) in
        let exprExtraInfo := (eval hnf in exprExtraInfo) in
        let pident_pair := build_pident_pair exprExtraInfo pkg in
        let ident_interp := (eval cbv [Classes.ident_interp] in (@Classes.ident_interp exprInfo)) in
        let ident_interp_head := head ident_interp in
        let base_interp_beq := (eval cbv [Classes.base_interp_beq] in (@Classes.base_interp_beq exprInfo exprExtraInfo)) in
        let base_interp_beq_head := head base_interp_beq in
        let x := fresh "x" in
        let v := (eval cbv -[ident_interp_head ident.smart_Literal base_interp_beq_head] in
                     (fun var
                      => @interp_rewrite_rules_folded
                           exprInfo exprExtraInfo pkg var pident_pair (fun evm t x => Datatypes.fst x))) in
        let v := (eval cbv [ident_interp_head ident.smart_Literal ident.ident_Literal ident.ident_tt ident.ident_pair] in v) in
        v.

      Module Import AdjustRewriteRulesForReduction.
        Import Rewriter.Util.PrimitiveHList.
         
        Ltac make_split_rewrite_rules rewrite_rules :=
          let split_rewrite_rules := fresh "split_rewrite_rules" in
          let v := constr:(fun var => split_list (rewrite_rules var)) in
          let h := head rewrite_rules in
          let do_reduce_rules := lazymatch h with
                                 | @cons => false
                                 | @nil => false
                                 | _ => true
                                 end in
          let v := lazymatch do_reduce_rules with
                   | true => (eval cbv [split_list projT1 projT2 h] in v)
                   | false => (eval cbv [split_list projT1 projT2] in v)
                   end in
          cache_term v split_rewrite_rules.
        Ltac make_pr1_rewrite_rules split_rewrite_rules :=
          let var := fresh "var" in
          constr:(fun var => ltac:(let v := (eval hnf in (projT1 (split_rewrite_rules var))) in
                                   exact v)).
        Ltac make_pr2_rewrite_rules split_rewrite_rules :=
          let pr2_rewrite_rules := fresh "pr2_rewrite_rules" in
          let var := fresh "var" in
          let v :=
              constr:(fun var
                      => ltac:(let v := (eval hnf in (projT2 (split_rewrite_rules var))) in
                               exact v)) in
          cache_term v pr2_rewrite_rules.

        Ltac make_all_rewrite_rules pkg pr1_rewrite_rules pr2_rewrite_rules :=
          let pkg_type := type of pkg in
          let ident := lazymatch (eval hnf in pkg_type) with @package ?base ?ident => ident end in
          let all_rewrite_rules := fresh "all_rewrite_rules" in
          let var := fresh "var" in
          cache_term
            (fun var
             => combine_hlist (P:=@Compile.rewrite_ruleTP _ ident var (@pattern_ident _ _ pkg) (@arg_types_of pkg)) (pr1_rewrite_rules var) (pr2_rewrite_rules var))
            all_rewrite_rules.
      End AdjustRewriteRulesForReduction.

      Ltac Reify reify_base reify_ident exprInfo exprExtraInfo pkg ident_is_var_like include_interp specs :=
        let exprInfo := (eval hnf in exprInfo) in
        let exprExtraInfo := (eval hnf in exprExtraInfo) in
        let pkg := (eval hnf in pkg) in
        lazymatch constr:((exprInfo, exprExtraInfo, pkg)) with
        | ({| Classes.base := ?base
              ; Classes.ident := ?ident
              ; Classes.base_interp := ?base_interp
           |}
           , {| Classes.base_interp_beq := ?base_interp_beq
                ; Classes.try_make_transport_base_cps := ?try_make_transport_base_cps
                ; Classes.baseHasNat := ?baseTypeHasNat
                ; Classes.buildIdent := ?buildIdent
                ; Classes.toRestrictedIdent := ?toRestrictedIdent
                ; Classes.buildEagerIdent := ?buildEagerIdent
                ; Classes.invertIdent := ?invertIdent
                ; Classes.baseHasNatCorrect := ?baseHasNatCorrect
                ; Classes.toFromRestrictedIdent := ?toFromRestrictedIdent
             |}
           , {| pattern_ident := ?pattern_ident
                ; arg_types_unfolded := ?arg_types_unfolded
                ; type_of_list_arg_types_beq_unfolded := ?type_of_list_arg_types_beq_unfolded
                ; of_typed_ident_unfolded := ?of_typed_ident_unfolded
                ; arg_types_of_typed_ident_unfolded := ?arg_types_of_typed_ident_unfolded
             |})
          => let base_type := constr:(Compilers.base.type base) in
             let reflect_ident_iota := constr:(@Compile.reflect_ident_iota base ident base_interp baseTypeHasNat buildIdent buildEagerIdent toRestrictedIdent toFromRestrictedIdent invertIdent baseHasNatCorrect try_make_transport_base_cps) in
             let lems := Reify.Reify_list base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pattern_ident arg_types_unfolded type_of_list_arg_types_beq_unfolded of_typed_ident_unfolded arg_types_of_typed_ident_unfolded reflect_ident_iota (fun var t => @SubstVarLike.is_recursively_var_or_ident base_type ident var ident_is_var_like (type.base t)) specs in
             lazymatch include_interp with
             | true
               => let myapp := (eval cbv [List.app] in (@List.app)) in
                  let interp_rewrite_rules := build_interp_rewrite_rules exprInfo exprExtraInfo pkg in
                  let res := (eval cbv beta iota in
                                 (fun var => myapp _ (@interp_rewrite_rules var) (lems var))) in
                  let len := lazymatch (eval compute in (fun var => List.length (@interp_rewrite_rules var))) with (fun _ => ?n) => n end in
                  let adjusted_specs := (eval cbv [List.app List.repeat] in
                                            (List.app
                                               (List.repeat (false, forall A (x : A), x = x) len))) in
                  constr:((len, adjusted_specs specs, res))
             | false => constr:((O, specs, lems))
             | _ => constr_fail_with ltac:(fun _ => fail 1 "Invalid value for include_interp (must be either true or false):" include_interp)
             end
        end.

      Ltac make_rewrite_head1 base_interp try_make_transport_base_cps base_beq pident_unify_unknown invert_bind_args_unknown rewrite_head0 pr2_rewrite_rules :=
        time_tac_in_constr_if_debug1
          ltac:(fun _
                => let rewrite_head1
                       := (eval cbv -[pr2_rewrite_rules
                                        base_interp try_make_transport_base_cps  
                                        base.interp base.try_make_transport_cps
                                        type.try_make_transport_cps
                                        pattern.type.unify_extracted
                                        Compile.option_type_type_beq
                                        Let_In Option.sequence Option.sequence_return
                                        UnderLets.splice UnderLets.to_expr
                                        Compile.option_bind' pident_unify_unknown invert_bind_args_unknown Compile.normalize_deep_rewrite_rule
                                        Compile.reflect UnderLets.reify_and_let_binds_base_cps Compile.reify Compile.reify_and_let_binds_cps
                                        Compile.value'
                                        SubstVarLike.is_recursively_var_or_ident
                                     ] in rewrite_head0) in
                   let rewrite_head1
                       := (eval cbn [type.try_make_transport_cps base.try_make_transport_cps]
                            in rewrite_head1) in
                   rewrite_head1).
      Ltac make_rewrite_head2 pident_unify_unknown invert_bind_args_unknown rewrite_head1 pr2_rewrite_rules :=
        time_tac_in_constr_if_debug1
          ltac:(fun _
                => let rewrite_head2
                       := (eval cbv [id
                                       pr2_rewrite_rules
                                       projT1 projT2
                                       cpsbind cpscall cps_option_bind cpsreturn
                                       PrimitiveProd.Primitive.fst PrimitiveProd.Primitive.snd
                                       pattern.type.subst_default pattern.base.subst_default pattern.base.lookup_default
                                       PositiveMap.add PositiveMap.find PositiveMap.empty
                                       PositiveSet.rev PositiveSet.rev_append
                                       Compile.eval_decision_tree
                                       Compile.eval_rewrite_rules
                                       Compile.expr_of_rawexpr
                                       Compile.normalize_deep_rewrite_rule
                                       Compile.option_bind' pident_unify_unknown invert_bind_args_unknown Compile.normalize_deep_rewrite_rule
                                       Compile.reveal_rawexpr_cps
                                       Compile.reveal_rawexpr_cps_gen
                                       Compile.rew_should_do_again
                                       Compile.rew_with_opt
                                       Compile.rew_under_lets
                                       Compile.rew_replacement
                                       Compile.rValueOrExpr
                                       Compile.swap_list
                                       Compile.type_of_rawexpr
                                       Compile.option_type_type_beq
                                       Compile.value
                                       Compile.value_of_rawexpr
                                       Compile.value_with_lets
                                       ident.smart_Literal
                                       type.try_transport_cps
                                    ] in rewrite_head1) in
                   rewrite_head2).
      Ltac make_rewrite_head3 base_interp try_make_transport_base_cps base_beq rewrite_head2 :=
        time_tac_in_constr_if_debug1
          ltac:(fun _
                => let rewrite_head3
                       := (eval cbn [id
                                       base_interp try_make_transport_base_cps base_beq
                                       cpsbind cpscall cps_option_bind cpsreturn
                                       Compile.reify Compile.reify_and_let_binds_cps Compile.reflect Compile.value'
                                       Option.sequence Option.sequence_return Option.bind
                                       UnderLets.reify_and_let_binds_base_cps
                                       UnderLets.splice UnderLets.splice_list UnderLets.to_expr
                                       base.interp
                                       option_beq
                                       type.try_make_transport_cps base.try_make_transport_cps
                                       Datatypes.fst Datatypes.snd
                                    ] in rewrite_head2) in
                   rewrite_head3).
      Ltac make_rewrite_head' base_interp try_make_transport_base_cps base_beq pident_unify_unknown invert_bind_args_unknown rewrite_head0 pr2_rewrite_rules :=
        let base_interp := head base_interp in
        let try_make_transport_base_cps := head try_make_transport_base_cps in
        let base_beq := head base_beq in
        let __ := debug2 ltac:(fun _ => idtac "rewrite_head0 ===" pr2_rewrite_rules) in
        let rewrite_head1 := make_rewrite_head1 base_interp try_make_transport_base_cps base_beq pident_unify_unknown invert_bind_args_unknown rewrite_head0 pr2_rewrite_rules in
        let __ := debug2 ltac:(fun _ => idtac "rewrite_head1 ===" rewrite_head1) in
        let rewrite_head2 := make_rewrite_head2 pident_unify_unknown invert_bind_args_unknown rewrite_head1 pr2_rewrite_rules in
        let __ := debug2 ltac:(fun _ => idtac "rewrite_head2 ===" rewrite_head2) in
        let rewrite_head3 := make_rewrite_head3 base_interp try_make_transport_base_cps base_beq rewrite_head2 in
        let __ := debug2 ltac:(fun _ => idtac "rewrite_head3 ===" rewrite_head3) in
        rewrite_head3.

      Ltac make_rewrite_head base_interp try_make_transport_base_cps base_beq ident pident_unify_unknown invert_bind_args_unknown skip_early_reduction rewrite_head0 pr2_rewrite_rules :=
        let rewrite_head := fresh "rewrite_head" in
        let var := fresh "var" in
        let do_again := fresh "do_again" in
        let t := fresh "t" in
        let idc := fresh "idc" in
        let v :=
            constr:(
              fun var (do_again : forall t, @expr.expr _ ident (@Compile.value _ ident var) (type.base t) -> @UnderLets.UnderLets _ ident var (@expr.expr _ ident var (type.base t)))
                  t (idc : ident t)
              => ltac:(
                   let rewrite_head0 := constr:(rewrite_head0 var do_again t idc) in
                   let pr2_rewrite_rules := head pr2_rewrite_rules in
                   let v := lazymatch skip_early_reduction with
                            | true => rewrite_head0
                            | false => make_rewrite_head' base_interp try_make_transport_base_cps base_beq pident_unify_unknown invert_bind_args_unknown rewrite_head0 pr2_rewrite_rules
                            | ?v => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-literal-boolean for skip_early_reduction:" v)
                            end in
                   exact v)) in
        cache_term v rewrite_head.

      Ltac Build_rewriter_dataT reify_package exprInfo exprExtraInfo pkg ident_is_var_like include_interp skip_early_reduction skip_early_reduction_no_dtree specs :=
        let pkg_type := type of pkg in
        let base := lazymatch (eval hnf in pkg_type) with @package ?base ?ident => base end in
        let ident := lazymatch (eval hnf in pkg_type) with @package ?base ?ident => ident end in
        let base_interp := lazymatch (eval hnf in exprInfo) with {| Classes.base_interp := ?base_interp |} => base_interp end in
        let try_make_transport_base_cps := lazymatch (eval hnf in exprExtraInfo) with {| Classes.try_make_transport_base_cps := ?try_make_transport_base_cps |} => try_make_transport_base_cps end in
        let base_beq := lazymatch (eval hnf in exprExtraInfo) with {| Classes.base_beq := ?base_beq |} => base_beq end in
        let invert_bind_args_unknown := lazymatch (eval hnf in pkg) with {| invert_bind_args_unknown := ?v |} => v end in
        let pident_unify_unknown := lazymatch (eval hnf in pkg) with {| unify_unknown := ?v |} => v end in
        let __ := debug1 ltac:(fun _ => idtac "Reifying...") in
        let specs_lems :=
          let reify_base := Basic.Tactic.reify_base_via_reify_package reify_package in
          let reify_ident := Basic.Tactic.reify_ident_via_reify_package reify_package in

          Reify reify_base reify_ident exprInfo exprExtraInfo pkg ident_is_var_like include_interp specs in
        let dummy_count := lazymatch specs_lems with (?n, ?specs, ?lems) => n end in
        let specs := lazymatch specs_lems with (?n, ?specs, ?lems) => specs end in
        let rewrite_rules := lazymatch specs_lems with (?n, ?specs, ?lems) => lems end in
        let rewrite_rules_names := fresh "rewrite_rules" in
        let rewrite_rules := cache_term rewrite_rules rewrite_rules_names in
        let __ := debug1 ltac:(fun _ => idtac "Compiling decision tree...") in
        let dtree := Compile.CompileRewrites base ident (@pattern_ident _ _ pkg) (@arg_types_of pkg) (@raw_ident _ _ pkg) (@strip_types_of pkg) (@raw_ident_beq_of pkg) rewrite_rules in
        let default_fuel := (eval compute in (List.length specs)) in
        let __ := debug1 ltac:(fun _ => idtac "Splitting rewrite rules...") in
        let split_rewrite_rules := make_split_rewrite_rules rewrite_rules in
        let pr1_rewrite_rules := make_pr1_rewrite_rules split_rewrite_rules in
        let pr2_rewrite_rules := make_pr2_rewrite_rules split_rewrite_rules in
        let all_rewrite_rules := make_all_rewrite_rules pkg pr1_rewrite_rules pr2_rewrite_rules in
        let __ := debug1 ltac:(fun _ => idtac "Assembling rewrite_head...") in
        let rewrite_head0 := fresh "rewrite_head0" in
        let var := fresh "var" in
        let rewrite_head0
            := cache_term
                 (fun var
                  => @Compile.assemble_identifier_rewriters base (@Classes.try_make_transport_base_cps exprInfo exprExtraInfo) (@Classes.base_beq exprInfo exprExtraInfo) ident var (@eta_ident_cps _ _ pkg) (@pattern_ident _ _ pkg) (@arg_types_of pkg) (@unify _ _ pkg) pident_unify_unknown (@raw_ident _ _ pkg) (@full_types_of pkg) (@invert_bind_args _ _ pkg) invert_bind_args_unknown (@type_of_of pkg) (@raw_to_typed_of pkg) (@is_simple_of pkg) (Some dtree) (all_rewrite_rules var))
                 rewrite_head0 in
        let __ := debug1 ltac:(fun _ => idtac "Reducing rewrite_head...") in
        let rewrite_head := make_rewrite_head base_interp try_make_transport_base_cps base_beq ident pident_unify_unknown invert_bind_args_unknown skip_early_reduction rewrite_head0 pr2_rewrite_rules in
        let __ := debug1 ltac:(fun _ => idtac "Assembling rewrite_head_no_dtree...") in
        let rewrite_head_no_dtree0 := fresh "rewrite_head_no_dtree0" in
        let var := fresh "var" in
        let rewrite_head_no_dtree0
            := cache_term
                 (fun var
                  => @Compile.assemble_identifier_rewriters base (@Classes.try_make_transport_base_cps exprInfo exprExtraInfo) (@Classes.base_beq exprInfo exprExtraInfo) ident var (@eta_ident_cps _ _ pkg) (@pattern_ident _ _ pkg) (@arg_types_of pkg) (@unify _ _ pkg) pident_unify_unknown (@raw_ident _ _ pkg) (@full_types_of pkg) (@invert_bind_args _ _ pkg) invert_bind_args_unknown (@type_of_of pkg) (@raw_to_typed_of pkg) (@is_simple_of pkg) None (all_rewrite_rules var))
                 rewrite_head_no_dtree0 in
        let __ := debug1 ltac:(fun _ => idtac "Reducing rewrite_head_no_dtree...") in
        let rewrite_head_no_dtree := make_rewrite_head base_interp try_make_transport_base_cps base_beq ident pident_unify_unknown invert_bind_args_unknown skip_early_reduction_no_dtree rewrite_head_no_dtree0 pr2_rewrite_rules in
        constr:(@Build_rewriter_dataT'
                  exprInfo exprExtraInfo
                  pkg
                  ident_is_var_like
                  specs dummy_count dtree
                  rewrite_rules all_rewrite_rules eq_refl
                  default_fuel
                  rewrite_head eq_refl
                  rewrite_head_no_dtree eq_refl).

      Module Export Tactic.
        Module Export Settings.
          Global Arguments base.try_make_transport_cps _ !_ !_.
          Global Arguments type.try_make_transport_cps _ _ _ !_ !_.
          Global Arguments Option.sequence A !v1 v2.
          Global Arguments Option.sequence_return A !v1 v2.
          Global Arguments Option.bind A B !_ _.
          Global Arguments id / .
        End Settings.

        Tactic Notation "make_rewriter_data" constr(reify_package) constr(exprInfo) constr(exprExtraInfo) constr(pkg) constr(ident_is_var_like) constr(include_interp) constr(skip_early_reduction) constr(skip_early_reduction_no_dtree) constr(specs) :=
          let res := Build_rewriter_dataT reify_package exprInfo exprExtraInfo pkg ident_is_var_like include_interp skip_early_reduction skip_early_reduction_no_dtree specs in refine res.
      End Tactic.
    End Make.
    Export Make.GoalType.
    Import Make.Tactic.

    Ltac Build_RewriterT reify_package exprInfo exprExtraInfo pkg ident_is_var_like include_interp skip_early_reduction skip_early_reduction_no_dtree specs :=
      let pkg := (eval hnf in pkg) in
      let rewriter_data := fresh "rewriter_data" in
      let data := Make.Build_rewriter_dataT reify_package exprInfo exprExtraInfo pkg ident_is_var_like include_interp skip_early_reduction skip_early_reduction_no_dtree specs in
      let Rewrite_name := fresh "Rewriter" in
      let Rewrite := (eval cbv [Make.Rewrite rewrite_head Make.GoalType.ident_is_var_like Classes.base Classes.base_interp Classes.ident Classes.buildIdent Classes.invertIdent Classes.try_make_transport_base_cps default_fuel] in (@Make.Rewrite exprInfo exprExtraInfo pkg data)) in
      let Rewrite := cache_term Rewrite Rewrite_name in
      constr:(@Build_RewriterT exprInfo exprExtraInfo pkg data Rewrite eq_refl).

    Module Export Tactic.
      Module Export Settings.
        Export Make.Tactic.Settings.
      End Settings.

      Tactic Notation "make_Rewriter" constr(reify_package) constr(exprInfo) constr(exprExtraInfo) constr(pkg) constr(ident_is_var_like) constr(include_interp) constr(skip_early_reduction) constr(skip_early_reduction_no_dtree) constr(specs) :=
        let res := Build_RewriterT reify_package exprInfo exprExtraInfo pkg ident_is_var_like include_interp skip_early_reduction skip_early_reduction_no_dtree specs in refine res.
    End Tactic.
  End RewriteRules.
End Compilers.

End Reify.

End Rewriter_DOT_Rewriter_DOT_Reify_WRAPPED.
Module Export Rewriter_DOT_Rewriter_DOT_Reify.
Module Export Rewriter.
Module Export Rewriter.
Module Reify.
Include Rewriter_DOT_Rewriter_DOT_Reify_WRAPPED.Reify.
End Reify.

End Rewriter.

End Rewriter.

End Rewriter_DOT_Rewriter_DOT_Reify.
Import Coq.Lists.List.
Import Rewriter.Language.Pre.
Import Rewriter.Util.ListUtil.
Import ListNotations.

Import Pre.RewriteRuleNotations.

Lemma eval_list_rect_arrow
  : forall A P Q N C ls v,
    @list_rect_arrow_nodep A P Q N C ls v
    = ident.eagerly (@list_rect_arrow_nodep) A P Q N C ls v.
Admitted.

Lemma eval_list_rect
  : forall A P N C ls,
    @Thunked.list_rect A P N C ls
    = ident.eagerly (@Thunked.list_rect) A P N C ls.
Admitted.

Lemma eval_list_case_nil
  : forall A P N C, @Thunked.list_case A P N C nil = N tt.
Admitted.
Lemma eval_list_case_cons
  : forall A P N C x xs, @Thunked.list_case A P N C (x :: xs) = C x xs.
Admitted.

Lemma eval_list_nth_default
  : forall A default ls n,
    @List.nth_default A default ls ('n)
    = ident.eagerly (@List.nth_default) A default ls ('n).
Admitted.

Import Rewriter.Util.PrimitiveProd.
Global Instance eval_rect_list_rules : rules_proofs_for_eager_type list.
exact (existT (PrimitiveHList.hlist (@Datatypes.snd bool Prop))
              [Types.dont_do_again _; Types.dont_do_again _; Types.dont_do_again _; Types.dont_do_again _; Types.dont_do_again _]
              (@eval_list_rect_arrow, (@eval_list_rect, (@eval_list_case_nil, (@eval_list_case_cons, (@eval_list_nth_default, tt)))))%primproj).
Defined.
Export IdentifiersBasicGenerate.Compilers.
Module Export RewriterBuildRegistry.
Ltac make_scraped_data_with_args := Basic.ScrapeTactics.make_scrape_data.
Ltac make_rules_proofs_with_args := Basic.ScrapeTactics.make_rules_proofsT_with_args.
Import Coq.ZArith.ZArith.

Lemma map_eagerly_rect
  : forall A B f ls, @List.map A B f ls
                     = (ident.eagerly (@list_rect) _ _)
                         []
                         (fun x xs map_f_xs => f x :: map_f_xs)
                         ls.
Admitted.

Lemma app_eagerly_rect
  : forall A xs ys, @List.app A xs ys
                    = (ident.eagerly (@list_rect) _ _)
                        ys (fun x xs app_xs_ys => x :: app_xs_ys) xs.
Admitted.

Lemma flat_map_rect
  : forall A B f xs,
    @List.flat_map A B f xs
    = (list_rect (fun _ => _))
        nil
        (fun x _ flat_map_tl => f x ++ flat_map_tl)%list
        xs.
Admitted.

  Definition rules_proofs :=
    Eval cbv [projT2] in
      projT2
        (ltac:(RewriterBuildRegistry.make_rules_proofs_with_args)
          : Pre.rules_proofsT_with_args
              (Z.add_0_r
                , (@Prod.fst_pair)
                , (@Prod.snd_pair)
                , map_eagerly_rect
                , app_eagerly_rect
                , eval_rect list
                , do_again flat_map_rect)).

  Definition scraped_data :=
    (ltac:(cbv [projT1]; RewriterBuildRegistry.make_scraped_data_with_args)
      : PreCommon.Pre.ScrapedData.t_with_args
          rules_proofs
            false).
  Inductive base : Set :=  base_Z : base | base_nat0 : base | base_bool0 : base.
  Inductive ident : forall _ : type.type (base.type.type base), Type :=
    ident_false0 : ident
                     (@type.base (base.type.type base)
                        (@base.type.type_base base base_bool0))
  | ident_flat_map : forall t t0 : base.type.type base,
                     ident
                       (@type.arrow (base.type.type base)
                          (@type.arrow (base.type.type base)
                             (@type.base (base.type.type base) t)
                             (@type.base (base.type.type base)
                                (@base.type.list base t0)))
                          (@type.arrow (base.type.type base)
                             (@type.base (base.type.type base)
                                (@base.type.list base t))
                             (@type.base (base.type.type base)
                                (@base.type.list base t0))))
  | ident_app : forall t : base.type.type base,
                ident
                  (@type.arrow (base.type.type base)
                     (@type.base (base.type.type base) (@base.type.list base t))
                     (@type.arrow (base.type.type base)
                        (@type.base (base.type.type base) (@base.type.list base t))
                        (@type.base (base.type.type base) (@base.type.list base t))))
  | ident_map : forall t t0 : base.type.type base,
                ident
                  (@type.arrow (base.type.type base)
                     (@type.arrow (base.type.type base)
                        (@type.base (base.type.type base) t)
                        (@type.base (base.type.type base) t0))
                     (@type.arrow (base.type.type base)
                        (@type.base (base.type.type base) (@base.type.list base t))
                        (@type.base (base.type.type base) (@base.type.list base t0))))
  | ident_snd : forall t t0 : base.type.type base,
                ident
                  (@type.arrow (base.type.type base)
                     (@type.base (base.type.type base) (@base.type.prod base t t0))
                     (@type.base (base.type.type base) t0))
  | ident_fst : forall t t0 : base.type.type base,
                ident
                  (@type.arrow (base.type.type base)
                     (@type.base (base.type.type base) (@base.type.prod base t t0))
                     (@type.base (base.type.type base) t))
  | ident_Z0 : ident
                 (@type.base (base.type.type base)
                    (@base.type.type_base base base_Z))
  | ident_add : ident
                  (@type.arrow (base.type.type base)
                     (@type.base (base.type.type base)
                        (@base.type.type_base base base_Z))
                     (@type.arrow (base.type.type base)
                        (@type.base (base.type.type base)
                           (@base.type.type_base base base_Z))
                        (@type.base (base.type.type base)
                           (@base.type.type_base base base_Z))))
  | ident_literal0 : forall (t : base)
                       (_ : match t return Type with
                            | base_Z => Z
                            | base_nat0 => nat
                            | base_bool0 => bool
                            end),
                     ident
                       (@type.base (base.type.type base)
                          (@base.type.type_base base t))
  | ident_nil0 : forall t : base.type.type base,
                 ident (@type.base (base.type.type base) (@base.type.list base t))
  | ident_cons0 : forall t : base.type.type base,
                  ident
                    (@type.arrow (base.type.type base)
                       (@type.base (base.type.type base) t)
                       (@type.arrow (base.type.type base)
                          (@type.base (base.type.type base)
                             (@base.type.list base t))
                          (@type.base (base.type.type base)
                             (@base.type.list base t))))
  | ident_Some0 : forall t : base.type.type base,
                  ident
                    (@type.arrow (base.type.type base)
                       (@type.base (base.type.type base) t)
                       (@type.base (base.type.type base) (@base.type.option base t)))
  | ident_None0 : forall t : base.type.type base,
                  ident
                    (@type.base (base.type.type base) (@base.type.option base t))
  | ident_pair0 : forall t t0 : base.type.type base,
                  ident
                    (@type.arrow (base.type.type base)
                       (@type.base (base.type.type base) t)
                       (@type.arrow (base.type.type base)
                          (@type.base (base.type.type base) t0)
                          (@type.base (base.type.type base)
                             (@base.type.prod base t t0))))
  | ident_tt0 : ident (@type.base (base.type.type base) (@base.type.unit base))
  | ident_prod_rect_nodep0 : forall t t0 t1 : base.type.type base,
                             ident
                               (@type.arrow (base.type.type base)
                                  (@type.arrow (base.type.type base)
                                     (@type.base (base.type.type base) t)
                                     (@type.arrow (base.type.type base)
                                        (@type.base (base.type.type base) t0)
                                        (@type.base (base.type.type base) t1)))
                                  (@type.arrow (base.type.type base)
                                     (@type.base (base.type.type base)
                                        (@base.type.prod base t t0))
                                     (@type.base (base.type.type base) t1)))
  | ident_bool_rect0 : forall t : base.type.type base,
                       ident
                         (@type.arrow (base.type.type base)
                            (@type.arrow (base.type.type base)
                               (@type.base (base.type.type base)
                                  (@base.type.unit base))
                               (@type.base (base.type.type base) t))
                            (@type.arrow (base.type.type base)
                               (@type.arrow (base.type.type base)
                                  (@type.base (base.type.type base)
                                     (@base.type.unit base))
                                  (@type.base (base.type.type base) t))
                               (@type.arrow (base.type.type base)
                                  (@type.base (base.type.type base)
                                     (@base.type.type_base base base_bool0))
                                  (@type.base (base.type.type base) t))))
  | ident_list_case0 : forall t t0 : base.type.type base,
                       ident
                         (@type.arrow (base.type.type base)
                            (@type.arrow (base.type.type base)
                               (@type.base (base.type.type base)
                                  (@base.type.unit base))
                               (@type.base (base.type.type base) t0))
                            (@type.arrow (base.type.type base)
                               (@type.arrow (base.type.type base)
                                  (@type.base (base.type.type base) t)
                                  (@type.arrow (base.type.type base)
                                     (@type.base (base.type.type base)
                                        (@base.type.list base t))
                                     (@type.base (base.type.type base) t0)))
                               (@type.arrow (base.type.type base)
                                  (@type.base (base.type.type base)
                                     (@base.type.list base t))
                                  (@type.base (base.type.type base) t0))))
  | ident_option_rect0 : forall t t0 : base.type.type base,
                         ident
                           (@type.arrow (base.type.type base)
                              (@type.arrow (base.type.type base)
                                 (@type.base (base.type.type base) t)
                                 (@type.base (base.type.type base) t0))
                              (@type.arrow (base.type.type base)
                                 (@type.arrow (base.type.type base)
                                    (@type.base (base.type.type base)
                                       (@base.type.unit base))
                                    (@type.base (base.type.type base) t0))
                                 (@type.arrow (base.type.type base)
                                    (@type.base (base.type.type base)
                                       (@base.type.option base t))
                                    (@type.base (base.type.type base) t0))))
  | ident_nat_rect0 : forall t : base.type.type base,
                      ident
                        (@type.arrow (base.type.type base)
                           (@type.arrow (base.type.type base)
                              (@type.base (base.type.type base)
                                 (@base.type.unit base))
                              (@type.base (base.type.type base) t))
                           (@type.arrow (base.type.type base)
                              (@type.arrow (base.type.type base)
                                 (@type.base (base.type.type base)
                                    (@base.type.type_base base base_nat0))
                                 (@type.arrow (base.type.type base)
                                    (@type.base (base.type.type base) t)
                                    (@type.base (base.type.type base) t)))
                              (@type.arrow (base.type.type base)
                                 (@type.base (base.type.type base)
                                    (@base.type.type_base base base_nat0))
                                 (@type.base (base.type.type base) t))))
  | ident_eager_nat_rect0 : forall t : base.type.type base,
                            ident
                              (@type.arrow (base.type.type base)
                                 (@type.arrow (base.type.type base)
                                    (@type.base (base.type.type base)
                                       (@base.type.unit base))
                                    (@type.base (base.type.type base) t))
                                 (@type.arrow (base.type.type base)
                                    (@type.arrow (base.type.type base)
                                       (@type.base (base.type.type base)
                                          (@base.type.type_base base base_nat0))
                                       (@type.arrow (base.type.type base)
                                          (@type.base (base.type.type base) t)
                                          (@type.base (base.type.type base) t)))
                                    (@type.arrow (base.type.type base)
                                       (@type.base (base.type.type base)
                                          (@base.type.type_base base base_nat0))
                                       (@type.base (base.type.type base) t))))
  | ident_nat_rect_arrow0 : forall t t0 : base.type.type base,
                            ident
                              (@type.arrow (base.type.type base)
                                 (@type.arrow (base.type.type base)
                                    (@type.base (base.type.type base) t)
                                    (@type.base (base.type.type base) t0))
                                 (@type.arrow (base.type.type base)
                                    (@type.arrow (base.type.type base)
                                       (@type.base (base.type.type base)
                                          (@base.type.type_base base base_nat0))
                                       (@type.arrow (base.type.type base)
                                          (@type.arrow
                                             (base.type.type base)
                                             (@type.base (base.type.type base) t)
                                             (@type.base (base.type.type base) t0))
                                          (@type.arrow
                                             (base.type.type base)
                                             (@type.base (base.type.type base) t)
                                             (@type.base (base.type.type base) t0))))
                                    (@type.arrow (base.type.type base)
                                       (@type.base (base.type.type base)
                                          (@base.type.type_base base base_nat0))
                                       (@type.arrow (base.type.type base)
                                          (@type.base (base.type.type base) t)
                                          (@type.base (base.type.type base) t0)))))
  | ident_eager_nat_rect_arrow0 : forall t t0 : base.type.type base,
                                  ident
                                    (@type.arrow (base.type.type base)
                                       (@type.arrow (base.type.type base)
                                          (@type.base (base.type.type base) t)
                                          (@type.base (base.type.type base) t0))
                                       (@type.arrow (base.type.type base)
                                          (@type.arrow
                                             (base.type.type base)
                                             (@type.base
                                                (base.type.type base)
                                                (@base.type.type_base base
                                                   base_nat0))
                                             (@type.arrow
                                                (base.type.type base)
                                                (@type.arrow
                                                   (base.type.type base)
                                                   (@type.base
                                                      (base.type.type base) t)
                                                   (@type.base
                                                      (base.type.type base) t0))
                                                (@type.arrow
                                                   (base.type.type base)
                                                   (@type.base
                                                      (base.type.type base) t)
                                                   (@type.base
                                                      (base.type.type base) t0))))
                                          (@type.arrow
                                             (base.type.type base)
                                             (@type.base
                                                (base.type.type base)
                                                (@base.type.type_base base
                                                   base_nat0))
                                             (@type.arrow
                                                (base.type.type base)
                                                (@type.base (base.type.type base) t)
                                                (@type.base
                                                   (base.type.type base) t0)))))
  | ident_list_rect0 : forall t t0 : base.type.type base,
                       ident
                         (@type.arrow (base.type.type base)
                            (@type.arrow (base.type.type base)
                               (@type.base (base.type.type base)
                                  (@base.type.unit base))
                               (@type.base (base.type.type base) t0))
                            (@type.arrow (base.type.type base)
                               (@type.arrow (base.type.type base)
                                  (@type.base (base.type.type base) t)
                                  (@type.arrow (base.type.type base)
                                     (@type.base (base.type.type base)
                                        (@base.type.list base t))
                                     (@type.arrow (base.type.type base)
                                        (@type.base (base.type.type base) t0)
                                        (@type.base (base.type.type base) t0))))
                               (@type.arrow (base.type.type base)
                                  (@type.base (base.type.type base)
                                     (@base.type.list base t))
                                  (@type.base (base.type.type base) t0))))
  | ident_eager_list_rect0 : forall t t0 : base.type.type base,
                             ident
                               (@type.arrow (base.type.type base)
                                  (@type.arrow (base.type.type base)
                                     (@type.base (base.type.type base)
                                        (@base.type.unit base))
                                     (@type.base (base.type.type base) t0))
                                  (@type.arrow (base.type.type base)
                                     (@type.arrow (base.type.type base)
                                        (@type.base (base.type.type base) t)
                                        (@type.arrow (base.type.type base)
                                           (@type.base
                                              (base.type.type base)
                                              (@base.type.list base t))
                                           (@type.arrow
                                              (base.type.type base)
                                              (@type.base (base.type.type base) t0)
                                              (@type.base (base.type.type base) t0))))
                                     (@type.arrow (base.type.type base)
                                        (@type.base (base.type.type base)
                                           (@base.type.list base t))
                                        (@type.base (base.type.type base) t0))))
  | ident_list_rect_arrow0 : forall t t0 t1 : base.type.type base,
                             ident
                               (@type.arrow (base.type.type base)
                                  (@type.arrow (base.type.type base)
                                     (@type.base (base.type.type base) t0)
                                     (@type.base (base.type.type base) t1))
                                  (@type.arrow (base.type.type base)
                                     (@type.arrow (base.type.type base)
                                        (@type.base (base.type.type base) t)
                                        (@type.arrow (base.type.type base)
                                           (@type.base
                                              (base.type.type base)
                                              (@base.type.list base t))
                                           (@type.arrow
                                              (base.type.type base)
                                              (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                    (base.type.type base) t0)
                                                 (@type.base
                                                    (base.type.type base) t1))
                                              (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                    (base.type.type base) t0)
                                                 (@type.base
                                                    (base.type.type base) t1)))))
                                     (@type.arrow (base.type.type base)
                                        (@type.base (base.type.type base)
                                           (@base.type.list base t))
                                        (@type.arrow (base.type.type base)
                                           (@type.base (base.type.type base) t0)
                                           (@type.base (base.type.type base) t1)))))
  | ident_eager_list_rect_arrow0 : forall t t0 t1 : base.type.type base,
                                   ident
                                     (@type.arrow (base.type.type base)
                                        (@type.arrow (base.type.type base)
                                           (@type.base (base.type.type base) t0)
                                           (@type.base (base.type.type base) t1))
                                        (@type.arrow (base.type.type base)
                                           (@type.arrow
                                              (base.type.type base)
                                              (@type.base (base.type.type base) t)
                                              (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                    (base.type.type base)
                                                    (@base.type.list base t))
                                                 (@type.arrow
                                                    (base.type.type base)
                                                    (@type.arrow
                                                      (base.type.type base)
                                                      (@type.base
                                                      (base.type.type base) t0)
                                                      (@type.base
                                                      (base.type.type base) t1))
                                                    (@type.arrow
                                                      (base.type.type base)
                                                      (@type.base
                                                      (base.type.type base) t0)
                                                      (@type.base
                                                      (base.type.type base) t1)))))
                                           (@type.arrow
                                              (base.type.type base)
                                              (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                              (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                    (base.type.type base) t0)
                                                 (@type.base
                                                    (base.type.type base) t1)))))
  | ident_List_nth_default0 : forall t : base.type.type base,
                              ident
                                (@type.arrow (base.type.type base)
                                   (@type.base (base.type.type base) t)
                                   (@type.arrow (base.type.type base)
                                      (@type.base (base.type.type base)
                                         (@base.type.list base t))
                                      (@type.arrow (base.type.type base)
                                         (@type.base (base.type.type base)
                                            (@base.type.type_base base base_nat0))
                                         (@type.base (base.type.type base) t))))
  | ident_eager_List_nth_default0 : forall t : base.type.type base,
                                    ident
                                      (@type.arrow (base.type.type base)
                                         (@type.base (base.type.type base) t)
                                         (@type.arrow (base.type.type base)
                                            (@type.base
                                               (base.type.type base)
                                               (@base.type.list base t))
                                            (@type.arrow
                                               (base.type.type base)
                                               (@type.base
                                                  (base.type.type base)
                                                  (@base.type.type_base base
                                                     base_nat0))
                                               (@type.base (base.type.type base) t)))).
Inductive raw_ident : Set :=
    raw_ident_false0 : raw_ident
  | raw_ident_flat_map : raw_ident
  | raw_ident_app : raw_ident
  | raw_ident_map : raw_ident
  | raw_ident_snd : raw_ident
  | raw_ident_fst : raw_ident
  | raw_ident_Z0 : raw_ident
  | raw_ident_add : raw_ident
  | raw_ident_literal0 : raw_ident
  | raw_ident_nil0 : raw_ident
  | raw_ident_cons0 : raw_ident
  | raw_ident_Some0 : raw_ident
  | raw_ident_None0 : raw_ident
  | raw_ident_pair0 : raw_ident
  | raw_ident_tt0 : raw_ident
  | raw_ident_prod_rect_nodep0 : raw_ident
  | raw_ident_bool_rect0 : raw_ident
  | raw_ident_list_case0 : raw_ident
  | raw_ident_option_rect0 : raw_ident
  | raw_ident_nat_rect0 : raw_ident
  | raw_ident_eager_nat_rect0 : raw_ident
  | raw_ident_nat_rect_arrow0 : raw_ident
  | raw_ident_eager_nat_rect_arrow0 : raw_ident
  | raw_ident_list_rect0 : raw_ident
  | raw_ident_eager_list_rect0 : raw_ident
  | raw_ident_list_rect_arrow0 : raw_ident
  | raw_ident_eager_list_rect_arrow0 : raw_ident
  | raw_ident_List_nth_default0 : raw_ident
  | raw_ident_eager_List_nth_default0 : raw_ident.
Inductive
pattern_ident : forall _ : type.type (pattern.base.type.type base), Type :=
    pattern_ident_false0 : pattern_ident
                             (@type.base (pattern.base.type.type base)
                                (@pattern.base.type.type_base base base_bool0))
  | pattern_ident_flat_map : forall t t0 : pattern.base.type.type base,
                             pattern_ident
                               (@type.arrow (pattern.base.type.type base)
                                  (@type.arrow (pattern.base.type.type base)
                                     (@type.base (pattern.base.type.type base) t)
                                     (@type.base (pattern.base.type.type base)
                                        (@pattern.base.type.list base t0)))
                                  (@type.arrow (pattern.base.type.type base)
                                     (@type.base (pattern.base.type.type base)
                                        (@pattern.base.type.list base t))
                                     (@type.base (pattern.base.type.type base)
                                        (@pattern.base.type.list base t0))))
  | pattern_ident_app : forall t : pattern.base.type.type base,
                        pattern_ident
                          (@type.arrow (pattern.base.type.type base)
                             (@type.base (pattern.base.type.type base)
                                (@pattern.base.type.list base t))
                             (@type.arrow (pattern.base.type.type base)
                                (@type.base (pattern.base.type.type base)
                                   (@pattern.base.type.list base t))
                                (@type.base (pattern.base.type.type base)
                                   (@pattern.base.type.list base t))))
  | pattern_ident_map : forall t t0 : pattern.base.type.type base,
                        pattern_ident
                          (@type.arrow (pattern.base.type.type base)
                             (@type.arrow (pattern.base.type.type base)
                                (@type.base (pattern.base.type.type base) t)
                                (@type.base (pattern.base.type.type base) t0))
                             (@type.arrow (pattern.base.type.type base)
                                (@type.base (pattern.base.type.type base)
                                   (@pattern.base.type.list base t))
                                (@type.base (pattern.base.type.type base)
                                   (@pattern.base.type.list base t0))))
  | pattern_ident_snd : forall t t0 : pattern.base.type.type base,
                        pattern_ident
                          (@type.arrow (pattern.base.type.type base)
                             (@type.base (pattern.base.type.type base)
                                (@pattern.base.type.prod base t t0))
                             (@type.base (pattern.base.type.type base) t0))
  | pattern_ident_fst : forall t t0 : pattern.base.type.type base,
                        pattern_ident
                          (@type.arrow (pattern.base.type.type base)
                             (@type.base (pattern.base.type.type base)
                                (@pattern.base.type.prod base t t0))
                             (@type.base (pattern.base.type.type base) t))
  | pattern_ident_Z0 : pattern_ident
                         (@type.base (pattern.base.type.type base)
                            (@pattern.base.type.type_base base base_Z))
  | pattern_ident_add : pattern_ident
                          (@type.arrow (pattern.base.type.type base)
                             (@type.base (pattern.base.type.type base)
                                (@pattern.base.type.type_base base base_Z))
                             (@type.arrow (pattern.base.type.type base)
                                (@type.base (pattern.base.type.type base)
                                   (@pattern.base.type.type_base base base_Z))
                                (@type.base (pattern.base.type.type base)
                                   (@pattern.base.type.type_base base base_Z))))
  | pattern_ident_literal0 : forall t : base,
                             pattern_ident
                               (@type.base (pattern.base.type.type base)
                                  (@pattern.base.type.type_base base t))
  | pattern_ident_nil0 : forall t : pattern.base.type.type base,
                         pattern_ident
                           (@type.base (pattern.base.type.type base)
                              (@pattern.base.type.list base t))
  | pattern_ident_cons0 : forall t : pattern.base.type.type base,
                          pattern_ident
                            (@type.arrow (pattern.base.type.type base)
                               (@type.base (pattern.base.type.type base) t)
                               (@type.arrow (pattern.base.type.type base)
                                  (@type.base (pattern.base.type.type base)
                                     (@pattern.base.type.list base t))
                                  (@type.base (pattern.base.type.type base)
                                     (@pattern.base.type.list base t))))
  | pattern_ident_Some0 : forall t : pattern.base.type.type base,
                          pattern_ident
                            (@type.arrow (pattern.base.type.type base)
                               (@type.base (pattern.base.type.type base) t)
                               (@type.base (pattern.base.type.type base)
                                  (@pattern.base.type.option base t)))
  | pattern_ident_None0 : forall t : pattern.base.type.type base,
                          pattern_ident
                            (@type.base (pattern.base.type.type base)
                               (@pattern.base.type.option base t))
  | pattern_ident_pair0 : forall t t0 : pattern.base.type.type base,
                          pattern_ident
                            (@type.arrow (pattern.base.type.type base)
                               (@type.base (pattern.base.type.type base) t)
                               (@type.arrow (pattern.base.type.type base)
                                  (@type.base (pattern.base.type.type base) t0)
                                  (@type.base (pattern.base.type.type base)
                                     (@pattern.base.type.prod base t t0))))
  | pattern_ident_tt0 : pattern_ident
                          (@type.base (pattern.base.type.type base)
                             (@pattern.base.type.unit base))
  | pattern_ident_prod_rect_nodep0 : forall t t0 t1 : pattern.base.type.type base,
                                     pattern_ident
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.arrow
                                             (pattern.base.type.type base)
                                             (@type.base
                                                (pattern.base.type.type base) t)
                                             (@type.arrow
                                                (pattern.base.type.type base)
                                                (@type.base
                                                   (pattern.base.type.type base) t0)
                                                (@type.base
                                                   (pattern.base.type.type base) t1)))
                                          (@type.arrow
                                             (pattern.base.type.type base)
                                             (@type.base
                                                (pattern.base.type.type base)
                                                (@pattern.base.type.prod base t t0))
                                             (@type.base
                                                (pattern.base.type.type base) t1)))
  | pattern_ident_bool_rect0 : forall t : pattern.base.type.type base,
                               pattern_ident
                                 (@type.arrow (pattern.base.type.type base)
                                    (@type.arrow (pattern.base.type.type base)
                                       (@type.base (pattern.base.type.type base)
                                          (@pattern.base.type.unit base))
                                       (@type.base (pattern.base.type.type base) t))
                                    (@type.arrow (pattern.base.type.type base)
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.base (pattern.base.type.type base)
                                             (@pattern.base.type.unit base))
                                          (@type.base (pattern.base.type.type base)
                                             t))
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.base (pattern.base.type.type base)
                                             (@pattern.base.type.type_base base
                                                base_bool0))
                                          (@type.base (pattern.base.type.type base)
                                             t))))
  | pattern_ident_list_case0 : forall t t0 : pattern.base.type.type base,
                               pattern_ident
                                 (@type.arrow (pattern.base.type.type base)
                                    (@type.arrow (pattern.base.type.type base)
                                       (@type.base (pattern.base.type.type base)
                                          (@pattern.base.type.unit base))
                                       (@type.base (pattern.base.type.type base) t0))
                                    (@type.arrow (pattern.base.type.type base)
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.base (pattern.base.type.type base)
                                             t)
                                          (@type.arrow
                                             (pattern.base.type.type base)
                                             (@type.base
                                                (pattern.base.type.type base)
                                                (@pattern.base.type.list base t))
                                             (@type.base
                                                (pattern.base.type.type base) t0)))
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.base (pattern.base.type.type base)
                                             (@pattern.base.type.list base t))
                                          (@type.base (pattern.base.type.type base)
                                             t0))))
  | pattern_ident_option_rect0 : forall t t0 : pattern.base.type.type base,
                                 pattern_ident
                                   (@type.arrow (pattern.base.type.type base)
                                      (@type.arrow (pattern.base.type.type base)
                                         (@type.base (pattern.base.type.type base)
                                            t)
                                         (@type.base (pattern.base.type.type base)
                                            t0))
                                      (@type.arrow (pattern.base.type.type base)
                                         (@type.arrow (pattern.base.type.type base)
                                            (@type.base
                                               (pattern.base.type.type base)
                                               (@pattern.base.type.unit base))
                                            (@type.base
                                               (pattern.base.type.type base) t0))
                                         (@type.arrow (pattern.base.type.type base)
                                            (@type.base
                                               (pattern.base.type.type base)
                                               (@pattern.base.type.option base t))
                                            (@type.base
                                               (pattern.base.type.type base) t0))))
  | pattern_ident_nat_rect0 : forall t : pattern.base.type.type base,
                              pattern_ident
                                (@type.arrow (pattern.base.type.type base)
                                   (@type.arrow (pattern.base.type.type base)
                                      (@type.base (pattern.base.type.type base)
                                         (@pattern.base.type.unit base))
                                      (@type.base (pattern.base.type.type base) t))
                                   (@type.arrow (pattern.base.type.type base)
                                      (@type.arrow (pattern.base.type.type base)
                                         (@type.base (pattern.base.type.type base)
                                            (@pattern.base.type.type_base base
                                               base_nat0))
                                         (@type.arrow (pattern.base.type.type base)
                                            (@type.base
                                               (pattern.base.type.type base) t)
                                            (@type.base
                                               (pattern.base.type.type base) t)))
                                      (@type.arrow (pattern.base.type.type base)
                                         (@type.base (pattern.base.type.type base)
                                            (@pattern.base.type.type_base base
                                               base_nat0))
                                         (@type.base (pattern.base.type.type base)
                                            t))))
  | pattern_ident_eager_nat_rect0 : forall t : pattern.base.type.type base,
                                    pattern_ident
                                      (@type.arrow (pattern.base.type.type base)
                                         (@type.arrow (pattern.base.type.type base)
                                            (@type.base
                                               (pattern.base.type.type base)
                                               (@pattern.base.type.unit base))
                                            (@type.base
                                               (pattern.base.type.type base) t))
                                         (@type.arrow (pattern.base.type.type base)
                                            (@type.arrow
                                               (pattern.base.type.type base)
                                               (@type.base
                                                  (pattern.base.type.type base)
                                                  (@pattern.base.type.type_base
                                                     base base_nat0))
                                               (@type.arrow
                                                  (pattern.base.type.type base)
                                                  (@type.base
                                                     (pattern.base.type.type base)
                                                     t)
                                                  (@type.base
                                                     (pattern.base.type.type base)
                                                     t)))
                                            (@type.arrow
                                               (pattern.base.type.type base)
                                               (@type.base
                                                  (pattern.base.type.type base)
                                                  (@pattern.base.type.type_base
                                                     base base_nat0))
                                               (@type.base
                                                  (pattern.base.type.type base) t))))
  | pattern_ident_nat_rect_arrow0 : forall t t0 : pattern.base.type.type base,
                                    pattern_ident
                                      (@type.arrow (pattern.base.type.type base)
                                         (@type.arrow (pattern.base.type.type base)
                                            (@type.base
                                               (pattern.base.type.type base) t)
                                            (@type.base
                                               (pattern.base.type.type base) t0))
                                         (@type.arrow (pattern.base.type.type base)
                                            (@type.arrow
                                               (pattern.base.type.type base)
                                               (@type.base
                                                  (pattern.base.type.type base)
                                                  (@pattern.base.type.type_base
                                                     base base_nat0))
                                               (@type.arrow
                                                  (pattern.base.type.type base)
                                                  (@type.arrow
                                                     (pattern.base.type.type base)
                                                     (@type.base
                                                      (pattern.base.type.type base)
                                                      t)
                                                     (@type.base
                                                      (pattern.base.type.type base)
                                                      t0))
                                                  (@type.arrow
                                                     (pattern.base.type.type base)
                                                     (@type.base
                                                      (pattern.base.type.type base)
                                                      t)
                                                     (@type.base
                                                      (pattern.base.type.type base)
                                                      t0))))
                                            (@type.arrow
                                               (pattern.base.type.type base)
                                               (@type.base
                                                  (pattern.base.type.type base)
                                                  (@pattern.base.type.type_base
                                                     base base_nat0))
                                               (@type.arrow
                                                  (pattern.base.type.type base)
                                                  (@type.base
                                                     (pattern.base.type.type base)
                                                     t)
                                                  (@type.base
                                                     (pattern.base.type.type base)
                                                     t0)))))
  | pattern_ident_eager_nat_rect_arrow0 : forall t t0 : pattern.base.type.type base,
                                          pattern_ident
                                            (@type.arrow
                                               (pattern.base.type.type base)
                                               (@type.arrow
                                                  (pattern.base.type.type base)
                                                  (@type.base
                                                     (pattern.base.type.type base)
                                                     t)
                                                  (@type.base
                                                     (pattern.base.type.type base)
                                                     t0))
                                               (@type.arrow
                                                  (pattern.base.type.type base)
                                                  (@type.arrow
                                                     (pattern.base.type.type base)
                                                     (@type.base
                                                      (pattern.base.type.type base)
                                                      (@pattern.base.type.type_base
                                                      base base_nat0))
                                                     (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0))
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0))))
                                                  (@type.arrow
                                                     (pattern.base.type.type base)
                                                     (@type.base
                                                      (pattern.base.type.type base)
                                                      (@pattern.base.type.type_base
                                                      base base_nat0))
                                                     (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)))))
  | pattern_ident_list_rect0 : forall t t0 : pattern.base.type.type base,
                               pattern_ident
                                 (@type.arrow (pattern.base.type.type base)
                                    (@type.arrow (pattern.base.type.type base)
                                       (@type.base (pattern.base.type.type base)
                                          (@pattern.base.type.unit base))
                                       (@type.base (pattern.base.type.type base) t0))
                                    (@type.arrow (pattern.base.type.type base)
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.base (pattern.base.type.type base)
                                             t)
                                          (@type.arrow
                                             (pattern.base.type.type base)
                                             (@type.base
                                                (pattern.base.type.type base)
                                                (@pattern.base.type.list base t))
                                             (@type.arrow
                                                (pattern.base.type.type base)
                                                (@type.base
                                                   (pattern.base.type.type base) t0)
                                                (@type.base
                                                   (pattern.base.type.type base) t0))))
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.base (pattern.base.type.type base)
                                             (@pattern.base.type.list base t))
                                          (@type.base (pattern.base.type.type base)
                                             t0))))
  | pattern_ident_eager_list_rect0 : forall t t0 : pattern.base.type.type base,
                                     pattern_ident
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.arrow
                                             (pattern.base.type.type base)
                                             (@type.base
                                                (pattern.base.type.type base)
                                                (@pattern.base.type.unit base))
                                             (@type.base
                                                (pattern.base.type.type base) t0))
                                          (@type.arrow
                                             (pattern.base.type.type base)
                                             (@type.arrow
                                                (pattern.base.type.type base)
                                                (@type.base
                                                   (pattern.base.type.type base) t)
                                                (@type.arrow
                                                   (pattern.base.type.type base)
                                                   (@type.base
                                                      (pattern.base.type.type base)
                                                      (@pattern.base.type.list base
                                                      t))
                                                   (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0))))
                                             (@type.arrow
                                                (pattern.base.type.type base)
                                                (@type.base
                                                   (pattern.base.type.type base)
                                                   (@pattern.base.type.list base t))
                                                (@type.base
                                                   (pattern.base.type.type base) t0))))
  | pattern_ident_list_rect_arrow0 : forall t t0 t1 : pattern.base.type.type base,
                                     pattern_ident
                                       (@type.arrow (pattern.base.type.type base)
                                          (@type.arrow
                                             (pattern.base.type.type base)
                                             (@type.base
                                                (pattern.base.type.type base) t0)
                                             (@type.base
                                                (pattern.base.type.type base) t1))
                                          (@type.arrow
                                             (pattern.base.type.type base)
                                             (@type.arrow
                                                (pattern.base.type.type base)
                                                (@type.base
                                                   (pattern.base.type.type base) t)
                                                (@type.arrow
                                                   (pattern.base.type.type base)
                                                   (@type.base
                                                      (pattern.base.type.type base)
                                                      (@pattern.base.type.list base
                                                      t))
                                                   (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t1))
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t1)))))
                                             (@type.arrow
                                                (pattern.base.type.type base)
                                                (@type.base
                                                   (pattern.base.type.type base)
                                                   (@pattern.base.type.list base t))
                                                (@type.arrow
                                                   (pattern.base.type.type base)
                                                   (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)
                                                   (@type.base
                                                      (pattern.base.type.type base)
                                                      t1)))))
  | pattern_ident_eager_list_rect_arrow0 : forall
                                             t t0 t1 : pattern.base.type.type base,
                                           pattern_ident
                                             (@type.arrow
                                                (pattern.base.type.type base)
                                                (@type.arrow
                                                   (pattern.base.type.type base)
                                                   (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)
                                                   (@type.base
                                                      (pattern.base.type.type base)
                                                      t1))
                                                (@type.arrow
                                                   (pattern.base.type.type base)
                                                   (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t)
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      (@pattern.base.type.list base
                                                      t))
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t1))
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t1)))))
                                                   (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      (@pattern.base.type.list base
                                                      t))
                                                      (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t0)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t1)))))
  | pattern_ident_List_nth_default0 : forall t : pattern.base.type.type base,
                                      pattern_ident
                                        (@type.arrow (pattern.base.type.type base)
                                           (@type.base
                                              (pattern.base.type.type base) t)
                                           (@type.arrow
                                              (pattern.base.type.type base)
                                              (@type.base
                                                 (pattern.base.type.type base)
                                                 (@pattern.base.type.list base t))
                                              (@type.arrow
                                                 (pattern.base.type.type base)
                                                 (@type.base
                                                    (pattern.base.type.type base)
                                                    (@pattern.base.type.type_base
                                                      base base_nat0))
                                                 (@type.base
                                                    (pattern.base.type.type base) t))))
  | pattern_ident_eager_List_nth_default0 : forall t : pattern.base.type.type base,
                                            pattern_ident
                                              (@type.arrow
                                                 (pattern.base.type.type base)
                                                 (@type.base
                                                    (pattern.base.type.type base) t)
                                                 (@type.arrow
                                                    (pattern.base.type.type base)
                                                    (@type.base
                                                      (pattern.base.type.type base)
                                                      (@pattern.base.type.list base
                                                      t))
                                                    (@type.arrow
                                                      (pattern.base.type.type base)
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      (@pattern.base.type.type_base
                                                      base base_nat0))
                                                      (@type.base
                                                      (pattern.base.type.type base)
                                                      t)))).
Definition base_interp0 : forall _ : base, Type .
admit.
Defined.
Definition all_base_and_interp0 : list (prod base Type) .
Proof.
exact (
    @cons (prod base Type) (@pair base Type base_Z Z)
      (@cons (prod base Type) (@pair base Type base_nat0 nat)
         (@cons (prod base Type) (@pair base Type base_bool0 bool)
            (@nil (prod base Type)))) ).
Defined.
Definition ident_interp0 :
    forall (t : type.type (base.type.type base)) (_ : ident t),
    @type.interp (base.type.type base) (@base.interp base base_interp0) t .
Admitted.
Definition base_beq0 : forall (_ : base) (_ : base), bool .
Admitted.
Definition reflect_base_beq0 :
    forall x y : base, Bool.reflect (@eq base x y) (base_beq0 x y) .
Admitted.
Definition baseHasNat0 : base.type.BaseTypeHasNatT base .
Admitted.
Definition baseHasNatCorrect0 :
    @base.BaseHasNatCorrectT base base_interp0 baseHasNat0 .
Admitted.
Definition base_interp_beq0 :
    forall (t1 t2 : base) (_ : base_interp0 t1) (_ : base_interp0 t2), bool .
admit.
Defined.
Definition reflect_base_interp_beq0 :
    forall (t : base) (x y : base_interp0 t),
    Bool.reflect (@eq (base_interp0 t) x y) (base_interp_beq0 t t x y) .
Admitted.
Definition try_make_base_transport_cps0 : type.try_make_transport_cpsT base .
Admitted.
Definition try_make_base_transport_cps_correct0 :
    @type.try_make_transport_cps_correctT base base_beq0
      try_make_base_transport_cps0 reflect_base_beq0 .
Admitted.
Definition all_ident_and_interp0 :
    IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.t .
Proof.
exact (
    @IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
      (ident
         (@type.base (base.type.type base)
            (@base.type.type_base base base_bool0))) bool ident_false0 false
      (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
         (forall t t0 : base.type.type base,
          ident
            (@type.arrow (base.type.type base)
               (@type.arrow (base.type.type base)
                  (@type.base (base.type.type base) t)
                  (@type.base (base.type.type base) (@base.type.list base t0)))
               (@type.arrow (base.type.type base)
                  (@type.base (base.type.type base) (@base.type.list base t))
                  (@type.base (base.type.type base) (@base.type.list base t0)))))
         (forall (A B : Type) (_ : forall _ : A, list B) (_ : list A), list B)
         ident_flat_map flat_map
         (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
            (forall t : base.type.type base,
             ident
               (@type.arrow (base.type.type base)
                  (@type.base (base.type.type base) (@base.type.list base t))
                  (@type.arrow (base.type.type base)
                     (@type.base (base.type.type base)
                        (@base.type.list base t))
                     (@type.base (base.type.type base)
                        (@base.type.list base t)))))
            (forall (A : Type) (_ : list A) (_ : list A), list A) ident_app
            app
            (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
               (forall t t0 : base.type.type base,
                ident
                  (@type.arrow (base.type.type base)
                     (@type.arrow (base.type.type base)
                        (@type.base (base.type.type base) t)
                        (@type.base (base.type.type base) t0))
                     (@type.arrow (base.type.type base)
                        (@type.base (base.type.type base)
                           (@base.type.list base t))
                        (@type.base (base.type.type base)
                           (@base.type.list base t0)))))
               (forall (A B : Type) (_ : forall _ : A, B) (_ : list A),
                list B) ident_map map
               (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                  (forall t t0 : base.type.type base,
                   ident
                     (@type.arrow (base.type.type base)
                        (@type.base (base.type.type base)
                           (@base.type.prod base t t0))
                        (@type.base (base.type.type base) t0)))
                  (forall (A B : Type) (_ : prod A B), B) ident_snd
                  (@snd)
                  (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                     (forall t t0 : base.type.type base,
                      ident
                        (@type.arrow (base.type.type base)
                           (@type.base (base.type.type base)
                              (@base.type.prod base t t0))
                           (@type.base (base.type.type base) t)))
                     (forall (A B : Type) (_ : prod A B), A) ident_fst
                     (@fst)
                     (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                        (ident
                           (@type.base (base.type.type base)
                              (@base.type.type_base base base_Z))) Z ident_Z0
                        Z0
                        (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                           (ident
                              (@type.arrow (base.type.type base)
                                 (@type.base (base.type.type base)
                                    (@base.type.type_base base base_Z))
                                 (@type.arrow (base.type.type base)
                                    (@type.base (base.type.type base)
                                       (@base.type.type_base base base_Z))
                                    (@type.base (base.type.type base)
                                       (@base.type.type_base base base_Z)))))
                           (forall (_ : Z) (_ : Z), Z) ident_add Z.add
                           (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                              (forall (t : base)
                                 (_ : match t return Type with
                                      | base_Z => Z
                                      | base_nat0 => nat
                                      | base_bool0 => bool
                                      end),
                               ident
                                 (@type.base (base.type.type base)
                                    (@base.type.type_base base t)))
                              (forall (T : Type) (_ : T), T) ident_literal0
                              (@ident.literal)
                              (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                 (forall t : base.type.type base,
                                  ident
                                    (@type.base (base.type.type base)
                                       (@base.type.list base t)))
                                 (forall A : Type, list A) ident_nil0
                                 (@nil)
                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                    (forall t : base.type.type base,
                                     ident
                                       (@type.arrow
                                          (base.type.type base)
                                          (@type.base (base.type.type base) t)
                                          (@type.arrow
                                             (base.type.type base)
                                             (@type.base
                                                (base.type.type base)
                                                (@base.type.list base t))
                                             (@type.base
                                                (base.type.type base)
                                                (@base.type.list base t)))))
                                    (forall (A : Type) (_ : A) (_ : list A),
                                     list A) ident_cons0
                                    (@cons)
                                    (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                       (forall t : base.type.type base,
                                        ident
                                          (@type.arrow
                                             (base.type.type base)
                                             (@type.base
                                                (base.type.type base) t)
                                             (@type.base
                                                (base.type.type base)
                                                (@base.type.option base t))))
                                       (forall (A : Type) (_ : A), option A)
                                       ident_Some0
                                       (@Some)
                                       (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                          (forall t : base.type.type base,
                                           ident
                                             (@type.base
                                                (base.type.type base)
                                                (@base.type.option base t)))
                                          (forall A : Type, option A)
                                          ident_None0
                                          (@None)
                                          (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                             (forall
                                                t t0 : base.type.type base,
                                              ident
                                                (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.prod base t t0)))))
                                             (forall
                                                (A B : Type)
                                                (_ : A)
                                                (_ : B),
                                              prod A B) ident_pair0
                                             (@pair)
                                             (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                (ident
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base)))
                                                unit ident_tt0 tt
                                                (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0
                                                 t1 :
                                                 base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1)))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.prod base t t0))
                                                 (@type.base
                                                 (base.type.type base) t1))))
                                                 (forall
                                                 (A B P : Type)
                                                 (_ :
                                                 forall (_ : A) (_ : B), P)
                                                 (_ : prod A B), P)
                                                 ident_prod_rect_nodep0
                                                 (@Prod.prod_rect_nodep)
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base))
                                                 (@type.base
                                                 (base.type.type base) t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base))
                                                 (@type.base
                                                 (base.type.type base) t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_bool0))
                                                 (@type.base
                                                 (base.type.type base) t)))))
                                                 (forall
                                                 (P : Type)
                                                 (_ : forall _ : unit, P)
                                                 (_ : forall _ : unit, P)
                                                 (_ : bool), P)
                                                 ident_bool_rect0
                                                 Bool.Thunked.bool_rect
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0 : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base))
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.base
                                                 (base.type.type base) t0)))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.base
                                                 (base.type.type base) t0)))))
                                                 (forall
                                                 (A P : Type)
                                                 (_ : forall _ : unit, P)
                                                 (_ :
                                                 forall (_ : A) (_ : list A),
                                                 P) (_ : list A), P)
                                                 ident_list_case0
                                                 (@Thunked.list_case)
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0 : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base))
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.option base t))
                                                 (@type.base
                                                 (base.type.type base) t0)))))
                                                 (forall
                                                 (A P : Type)
                                                 (_ : forall _ : A, P)
                                                 (_ : forall _ : unit, P)
                                                 (_ : option A), P)
                                                 ident_option_rect0
                                                 (@Option.Thunked.option_rect)
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base))
                                                 (@type.base
                                                 (base.type.type base) t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t)))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.base
                                                 (base.type.type base) t)))))
                                                 (forall
                                                 (P : Type)
                                                 (_ : forall _ : unit, P)
                                                 (_ :
                                                 forall (_ : nat) (_ : P), P)
                                                 (_ : nat), P)
                                                 ident_nat_rect0
                                                 NatUtil.Thunked.nat_rect
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base))
                                                 (@type.base
                                                 (base.type.type base) t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t)))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.base
                                                 (base.type.type base) t)))))
                                                 (forall
                                                 (P : Type)
                                                 (_ : forall _ : unit, P)
                                                 (_ :
                                                 forall (_ : nat) (_ : P), P)
                                                 (_ : nat), P)
                                                 ident_eager_nat_rect0
                                                 (@ident.eagerly
                                                 (forall
                                                 (P : Type)
                                                 (_ : forall _ : unit, P)
                                                 (_ :
                                                 forall (_ : nat) (_ : P), P)
                                                 (_ : nat), P)
                                                 NatUtil.Thunked.nat_rect)
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0 : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))))))
                                                 (forall
                                                 (P Q : Type)
                                                 (_ : forall _ : P, Q)
                                                 (_ :
                                                 forall
                                                 (_ : nat)
                                                 (_ : forall _ : P, Q)
                                                 (_ : P), Q)
                                                 (_ : nat)
                                                 (_ : P), Q)
                                                 ident_nat_rect_arrow0
                                                 (@NatUtil.nat_rect_arrow_nodep)
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0 : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.base
                                                 (base.type.type base) t0))))))
                                                 (forall
                                                 (P Q : Type)
                                                 (_ : forall _ : P, Q)
                                                 (_ :
                                                 forall
                                                 (_ : nat)
                                                 (_ : forall _ : P, Q)
                                                 (_ : P), Q)
                                                 (_ : nat)
                                                 (_ : P), Q)
                                                 ident_eager_nat_rect_arrow0
                                                 (@ident.eagerly
                                                 (forall
                                                 (P Q : Type)
                                                 (_ : forall _ : P, Q)
                                                 (_ :
                                                 forall
                                                 (_ : nat)
                                                 (_ : forall _ : P, Q)
                                                 (_ : P), Q)
                                                 (_ : nat)
                                                 (_ : P), Q)
                                                 (@NatUtil.nat_rect_arrow_nodep))
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0 : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base))
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t0))))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.base
                                                 (base.type.type base) t0)))))
                                                 (forall
                                                 (A P : Type)
                                                 (_ : forall _ : unit, P)
                                                 (_ :
                                                 forall
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : P), P)
                                                 (_ : list A), P)
                                                 ident_list_rect0
                                                 (@Thunked.list_rect)
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0 : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.unit base))
                                                 (@type.base
                                                 (base.type.type base) t0))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t0))))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.base
                                                 (base.type.type base) t0)))))
                                                 (forall
                                                 (A P : Type)
                                                 (_ : forall _ : unit, P)
                                                 (_ :
                                                 forall
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : P), P)
                                                 (_ : list A), P)
                                                 ident_eager_list_rect0
                                                 (@ident.eagerly
                                                 (forall
                                                 (A P : Type)
                                                 (_ : forall _ : unit, P)
                                                 (_ :
                                                 forall
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : P), P)
                                                 (_ : list A), P)
                                                 (@Thunked.list_rect))
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0
                                                 t1 :
                                                 base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1)))))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1))))))
                                                 (forall
                                                 (A P Q : Type)
                                                 (_ : forall _ : P, Q)
                                                 (_ :
                                                 forall
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : forall _ : P, Q)
                                                 (_ : P), Q)
                                                 (_ : list A)
                                                 (_ : P), Q)
                                                 ident_list_rect_arrow0
                                                 (@list_rect_arrow_nodep)
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t t0
                                                 t1 :
                                                 base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1)))))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t0)
                                                 (@type.base
                                                 (base.type.type base) t1))))))
                                                 (forall
                                                 (A P Q : Type)
                                                 (_ : forall _ : P, Q)
                                                 (_ :
                                                 forall
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : forall _ : P, Q)
                                                 (_ : P), Q)
                                                 (_ : list A)
                                                 (_ : P), Q)
                                                 ident_eager_list_rect_arrow0
                                                 (@ident.eagerly
                                                 (forall
                                                 (A P Q : Type)
                                                 (_ : forall _ : P, Q)
                                                 (_ :
                                                 forall
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : forall _ : P, Q)
                                                 (_ : P), Q)
                                                 (_ : list A)
                                                 (_ : P), Q)
                                                 (@list_rect_arrow_nodep))
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.base
                                                 (base.type.type base) t)))))
                                                 (forall
                                                 (A : Type)
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : nat), A)
                                                 ident_List_nth_default0
                                                 nth_default
                                                 (@IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.cons
                                                 (forall
                                                 t : base.type.type base,
                                                 ident
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base) t)
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.list base t))
                                                 (@type.arrow
                                                 (base.type.type base)
                                                 (@type.base
                                                 (base.type.type base)
                                                 (@base.type.type_base base
                                                 base_nat0))
                                                 (@type.base
                                                 (base.type.type base) t)))))
                                                 (forall
                                                 (A : Type)
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : nat), A)
                                                 ident_eager_List_nth_default0
                                                 (@ident.eagerly
                                                 (forall
                                                 (A : Type)
                                                 (_ : A)
                                                 (_ : list A)
                                                 (_ : nat), A) nth_default)
                                                 IdentifiersBasicLibrary.Compilers.Basic.GallinaAndReifiedIdentList.nil))))))))))))))))))))))))))))
    ).
Defined.
Definition buildEagerIdent0 : @ident.BuildEagerIdentT base ident baseHasNat0 .
Admitted.
Definition buildInterpEagerIdentCorrect0 :
    @ident.BuildInterpEagerIdentCorrectT base base_interp0 ident
      ident_interp0 baseHasNat0 buildEagerIdent0 baseHasNatCorrect0 .
Admitted.
Definition toRestrictedIdent0 :
    @ident.ToRestrictedIdentT base ident baseHasNat0 .
Admitted.
Definition toFromRestrictedIdent0 :
    @ident.ToFromRestrictedIdentT base ident baseHasNat0 buildEagerIdent0
      toRestrictedIdent0 .
Admitted.
Definition buildIdent0 : @ident.BuildIdentT base base_interp0 ident .
Admitted.
Definition buildInterpIdentCorrect0 :
    @ident.BuildInterpIdentCorrectT base base_interp0 ident buildIdent0
      ident_interp0 .
Admitted.
Definition ident_is_var_like0 :
    forall (t : type.type (base.type.type base)) (_ : ident t), bool .
Admitted.
Definition ident_interp_Proper0 :
    forall t : type.type (base.type.type base),
    @Morphisms.Proper
      (forall _ : ident t,
       @type.interp (base.type.type base) (@base.interp base base_interp0) t)
      (@Morphisms.respectful (ident t)
         (@type.interp (base.type.type base) (@base.interp base base_interp0)
            t) (@eq (ident t))
         (@type.related (base.type.type base)
            (@base.interp base base_interp0)
            (fun t0 : base.type.type base =>
             @eq (@base.interp base base_interp0 t0)) t))
      (ident_interp0 t) .
Admitted.
Definition invertIdent0 : @invert_expr.InvertIdentT base base_interp0 ident .
Admitted.
Definition buildInvertIdentCorrect0 :
    @invert_expr.BuildInvertIdentCorrectT base base_interp0 ident
      invertIdent0 buildIdent0 .
Admitted.
Definition base_default0 : @DefaultValue.type.base.DefaultT base base_interp0 .
Admitted.
Definition all_base2 : list base .
Admitted.
Definition all_idents2 :
    list (@PrimitiveSigma.Primitive.sigT Type (fun T : Type => T)) .
Admitted.
Definition ident_index1 :
    forall (t : type.type (base.type.type base)) (_ : ident t), nat .
Admitted.
Definition eta_ident_cps_gen2 :
    forall
      (T : forall (t : type.type (base.type.type base)) (_ : ident t), Type)
      (f : forall (t : type.type (base.type.type base)) (idc : ident t),
           T t idc),
    @sig
      (forall (t : type.type (base.type.type base)) (idc : ident t), T t idc)
      (fun
         f' : forall (t : type.type (base.type.type base)) (idc : ident t),
              T t idc =>
       forall (t : type.type (base.type.type base)) (idc : ident t),
       @eq (T t idc) (f' t idc) (f t idc)) .
Admitted.
Definition eta_ident_cps_gen_expand_literal1 :
    forall
      (T : forall (t : type.type (base.type.type base)) (_ : ident t), Type)
      (f : forall (t : type.type (base.type.type base)) (idc : ident t),
           T t idc),
    @sig
      (forall (t : type.type (base.type.type base)) (idc : ident t), T t idc)
      (fun
         f' : forall (t : type.type (base.type.type base)) (idc : ident t),
              T t idc =>
       forall (t : type.type (base.type.type base)) (idc : ident t),
       @eq (T t idc) (f' t idc) (f t idc)) .
Admitted.
Definition eta_ident_cps0 :
    forall (T : forall _ : type.type (base.type.type base), Type)
      (t : type.type (base.type.type base)) (_ : ident t)
      (_ : forall (t0 : type.type (base.type.type base)) (_ : ident t0), T t0),
    T t .
Admitted.
Definition simple_idents0 :
    list
      (@PrimitiveSigma.Primitive.sigT (type.type (base.type.type base)) ident) .
Admitted.
Definition all_raw_idents0 : list raw_ident .
Admitted.
Definition ident_index2 : forall _ : raw_ident, nat .
Admitted.
Definition raw_ident_index_idempotent0 :
    forall idc : raw_ident,
    @eq (option raw_ident)
      (@nth_error raw_ident all_raw_idents0 (ident_index2 idc))
      (@Some raw_ident idc) .
Admitted.
Definition eta_ident_cps_gen3 :
    forall (T : forall _ : raw_ident, Type)
      (f : forall idc : raw_ident, T idc),
    @sig (forall idc : raw_ident, T idc)
      (fun f' : forall idc : raw_ident, T idc =>
       forall idc : raw_ident, @eq (T idc) (f' idc) (f idc)) .
Proof.
exact (
    fun (T : forall _ : raw_ident, Type) (f : forall idc : raw_ident, T idc)
    =>
    @exist (forall idc : raw_ident, T idc)
      (fun f' : forall idc : raw_ident, T idc =>
       forall idc : raw_ident, @eq (T idc) (f' idc) (f idc))
      (fun idc : raw_ident =>
       match idc as r return (T r) with
       | raw_ident_false0 => f raw_ident_false0
       | raw_ident_flat_map => f raw_ident_flat_map
       | raw_ident_app => f raw_ident_app
       | raw_ident_map => f raw_ident_map
       | raw_ident_snd => f raw_ident_snd
       | raw_ident_fst => f raw_ident_fst
       | raw_ident_Z0 => f raw_ident_Z0
       | raw_ident_add => f raw_ident_add
       | raw_ident_literal0 => f raw_ident_literal0
       | raw_ident_nil0 => f raw_ident_nil0
       | raw_ident_cons0 => f raw_ident_cons0
       | raw_ident_Some0 => f raw_ident_Some0
       | raw_ident_None0 => f raw_ident_None0
       | raw_ident_pair0 => f raw_ident_pair0
       | raw_ident_tt0 => f raw_ident_tt0
       | raw_ident_prod_rect_nodep0 => f raw_ident_prod_rect_nodep0
       | raw_ident_bool_rect0 => f raw_ident_bool_rect0
       | raw_ident_list_case0 => f raw_ident_list_case0
       | raw_ident_option_rect0 => f raw_ident_option_rect0
       | raw_ident_nat_rect0 => f raw_ident_nat_rect0
       | raw_ident_eager_nat_rect0 => f raw_ident_eager_nat_rect0
       | raw_ident_nat_rect_arrow0 => f raw_ident_nat_rect_arrow0
       | raw_ident_eager_nat_rect_arrow0 => f raw_ident_eager_nat_rect_arrow0
       | raw_ident_list_rect0 => f raw_ident_list_rect0
       | raw_ident_eager_list_rect0 => f raw_ident_eager_list_rect0
       | raw_ident_list_rect_arrow0 => f raw_ident_list_rect_arrow0
       | raw_ident_eager_list_rect_arrow0 =>
           f raw_ident_eager_list_rect_arrow0
       | raw_ident_List_nth_default0 => f raw_ident_List_nth_default0
       | raw_ident_eager_List_nth_default0 =>
           f raw_ident_eager_List_nth_default0
       end)
      (fun idc : raw_ident =>
       match
         idc as r
         return
           (@eq (T r)
              match r as r0 return (T r0) with
              | raw_ident_false0 => f raw_ident_false0
              | raw_ident_flat_map => f raw_ident_flat_map
              | raw_ident_app => f raw_ident_app
              | raw_ident_map => f raw_ident_map
              | raw_ident_snd => f raw_ident_snd
              | raw_ident_fst => f raw_ident_fst
              | raw_ident_Z0 => f raw_ident_Z0
              | raw_ident_add => f raw_ident_add
              | raw_ident_literal0 => f raw_ident_literal0
              | raw_ident_nil0 => f raw_ident_nil0
              | raw_ident_cons0 => f raw_ident_cons0
              | raw_ident_Some0 => f raw_ident_Some0
              | raw_ident_None0 => f raw_ident_None0
              | raw_ident_pair0 => f raw_ident_pair0
              | raw_ident_tt0 => f raw_ident_tt0
              | raw_ident_prod_rect_nodep0 => f raw_ident_prod_rect_nodep0
              | raw_ident_bool_rect0 => f raw_ident_bool_rect0
              | raw_ident_list_case0 => f raw_ident_list_case0
              | raw_ident_option_rect0 => f raw_ident_option_rect0
              | raw_ident_nat_rect0 => f raw_ident_nat_rect0
              | raw_ident_eager_nat_rect0 => f raw_ident_eager_nat_rect0
              | raw_ident_nat_rect_arrow0 => f raw_ident_nat_rect_arrow0
              | raw_ident_eager_nat_rect_arrow0 =>
                  f raw_ident_eager_nat_rect_arrow0
              | raw_ident_list_rect0 => f raw_ident_list_rect0
              | raw_ident_eager_list_rect0 => f raw_ident_eager_list_rect0
              | raw_ident_list_rect_arrow0 => f raw_ident_list_rect_arrow0
              | raw_ident_eager_list_rect_arrow0 =>
                  f raw_ident_eager_list_rect_arrow0
              | raw_ident_List_nth_default0 => f raw_ident_List_nth_default0
              | raw_ident_eager_List_nth_default0 =>
                  f raw_ident_eager_List_nth_default0
              end (f r))
       with
       | raw_ident_false0 =>
           @eq_refl (T raw_ident_false0) (f raw_ident_false0)
       | raw_ident_flat_map =>
           @eq_refl (T raw_ident_flat_map) (f raw_ident_flat_map)
       | raw_ident_app => @eq_refl (T raw_ident_app) (f raw_ident_app)
       | raw_ident_map => @eq_refl (T raw_ident_map) (f raw_ident_map)
       | raw_ident_snd => @eq_refl (T raw_ident_snd) (f raw_ident_snd)
       | raw_ident_fst => @eq_refl (T raw_ident_fst) (f raw_ident_fst)
       | raw_ident_Z0 => @eq_refl (T raw_ident_Z0) (f raw_ident_Z0)
       | raw_ident_add => @eq_refl (T raw_ident_add) (f raw_ident_add)
       | raw_ident_literal0 =>
           @eq_refl (T raw_ident_literal0) (f raw_ident_literal0)
       | raw_ident_nil0 => @eq_refl (T raw_ident_nil0) (f raw_ident_nil0)
       | raw_ident_cons0 => @eq_refl (T raw_ident_cons0) (f raw_ident_cons0)
       | raw_ident_Some0 => @eq_refl (T raw_ident_Some0) (f raw_ident_Some0)
       | raw_ident_None0 => @eq_refl (T raw_ident_None0) (f raw_ident_None0)
       | raw_ident_pair0 => @eq_refl (T raw_ident_pair0) (f raw_ident_pair0)
       | raw_ident_tt0 => @eq_refl (T raw_ident_tt0) (f raw_ident_tt0)
       | raw_ident_prod_rect_nodep0 =>
           @eq_refl (T raw_ident_prod_rect_nodep0)
             (f raw_ident_prod_rect_nodep0)
       | raw_ident_bool_rect0 =>
           @eq_refl (T raw_ident_bool_rect0) (f raw_ident_bool_rect0)
       | raw_ident_list_case0 =>
           @eq_refl (T raw_ident_list_case0) (f raw_ident_list_case0)
       | raw_ident_option_rect0 =>
           @eq_refl (T raw_ident_option_rect0) (f raw_ident_option_rect0)
       | raw_ident_nat_rect0 =>
           @eq_refl (T raw_ident_nat_rect0) (f raw_ident_nat_rect0)
       | raw_ident_eager_nat_rect0 =>
           @eq_refl (T raw_ident_eager_nat_rect0)
             (f raw_ident_eager_nat_rect0)
       | raw_ident_nat_rect_arrow0 =>
           @eq_refl (T raw_ident_nat_rect_arrow0)
             (f raw_ident_nat_rect_arrow0)
       | raw_ident_eager_nat_rect_arrow0 =>
           @eq_refl (T raw_ident_eager_nat_rect_arrow0)
             (f raw_ident_eager_nat_rect_arrow0)
       | raw_ident_list_rect0 =>
           @eq_refl (T raw_ident_list_rect0) (f raw_ident_list_rect0)
       | raw_ident_eager_list_rect0 =>
           @eq_refl (T raw_ident_eager_list_rect0)
             (f raw_ident_eager_list_rect0)
       | raw_ident_list_rect_arrow0 =>
           @eq_refl (T raw_ident_list_rect_arrow0)
             (f raw_ident_list_rect_arrow0)
       | raw_ident_eager_list_rect_arrow0 =>
           @eq_refl (T raw_ident_eager_list_rect_arrow0)
             (f raw_ident_eager_list_rect_arrow0)
       | raw_ident_List_nth_default0 =>
           @eq_refl (T raw_ident_List_nth_default0)
             (f raw_ident_List_nth_default0)
       | raw_ident_eager_List_nth_default0 =>
           @eq_refl (T raw_ident_eager_List_nth_default0)
             (f raw_ident_eager_List_nth_default0)
       end) ).
Defined.
Definition raw_ident_infos_of0 :
    forall _ : raw_ident,
    @IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_infos base ident .
Admitted.
Definition split_raw_ident_gen0 :
    forall (t : type.type (base.type.type base)) (idc : ident t),
    @PrimitiveSigma.Primitive.sigT raw_ident
      (fun ridc : raw_ident =>
       @sig
         (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args base
            ident
            (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _ _
               (raw_ident_infos_of0 ridc)))
         (fun
            args : @IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                     base ident
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                        _ _ (raw_ident_infos_of0 ridc)) =>
          @sig
            (@eq (type.type (base.type.type base))
               (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type _ _
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                     _ (raw_ident_infos_of0 ridc))
                  (@PrimitiveSigma.Primitive.projT1 _ _ args)
                  (@fst
                     (@fold_right Type Type (fun A B : Type => prod A B) unit
                        (@map
                           IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                           Type
                           (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                              base)
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                              _ _
                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                 _ _ (raw_ident_infos_of0 ridc)))))
                     (@fold_right Type Type (fun A B : Type => prod A B) unit
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                           _ _
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                              _ _ (raw_ident_infos_of0 ridc))
                           (@PrimitiveSigma.Primitive.projT1 _ _ args)))
                     (@PrimitiveSigma.Primitive.projT2 _ _ args))) t)
            (fun
               pf : @eq (type.type (base.type.type base))
                      (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                         _ _
                         (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                            _ _ (raw_ident_infos_of0 ridc))
                         (@PrimitiveSigma.Primitive.projT1 _ _ args)
                         (@fst
                            (@fold_right Type Type
                               (fun A B : Type => prod A B) unit
                               (@map
                                  IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                  Type
                                  (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                     base)
                                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                     _ _
                                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                        _ _ (raw_ident_infos_of0 ridc)))))
                            (@fold_right Type Type
                               (fun A B : Type => prod A B) unit
                               (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                  _ _
                                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                     _ _ (raw_ident_infos_of0 ridc))
                                  (@PrimitiveSigma.Primitive.projT1 _ _ args)))
                            (@PrimitiveSigma.Primitive.projT2 _ _ args))) t
             =>
             @eq (ident t) idc
               (@eq_rect (type.type (base.type.type base))
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type _
                     _
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                        _ _ (raw_ident_infos_of0 ridc))
                     (@PrimitiveSigma.Primitive.projT1 _ _ args)
                     (@fst
                        (@fold_right Type Type (fun A B : Type => prod A B)
                           unit
                           (@map
                              IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                              Type
                              (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                 base)
                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                 _ _
                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                    _ _ (raw_ident_infos_of0 ridc)))))
                        (@fold_right Type Type (fun A B : Type => prod A B)
                           unit
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                              _ _
                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                 _ _ (raw_ident_infos_of0 ridc))
                              (@PrimitiveSigma.Primitive.projT1 _ _ args)))
                        (@PrimitiveSigma.Primitive.projT2 _ _ args))) ident
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.assemble_ident
                     base ident
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                        _ _ (raw_ident_infos_of0 ridc)) args) t pf)))) .
Admitted.
Definition raw_invert_bind_args0 :
    forall (t : type.type (base.type.type base)) (_ : ident t)
      (pidc : raw_ident),
    option
      match pidc return Type with
      | raw_ident_false0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_false0
      | raw_ident_flat_map =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_flat_map
      | raw_ident_app =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_app
      | raw_ident_map =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_map
      | raw_ident_snd =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_snd
      | raw_ident_fst =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_fst
      | raw_ident_Z0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_Z0
      | raw_ident_add =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_add
      | raw_ident_literal0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_literal0
      | raw_ident_nil0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_nil0
      | raw_ident_cons0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_cons0
      | raw_ident_Some0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_Some0
      | raw_ident_None0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_None0
      | raw_ident_pair0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_pair0
      | raw_ident_tt0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_tt0
      | raw_ident_prod_rect_nodep0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_prod_rect_nodep0
      | raw_ident_bool_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_bool_rect0
      | raw_ident_list_case0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_list_case0
      | raw_ident_option_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_option_rect0
      | raw_ident_nat_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_nat_rect0
      | raw_ident_eager_nat_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_eager_nat_rect0
      | raw_ident_nat_rect_arrow0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_nat_rect_arrow0
      | raw_ident_eager_nat_rect_arrow0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0
            raw_ident_eager_nat_rect_arrow0
      | raw_ident_list_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_list_rect0
      | raw_ident_eager_list_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_eager_list_rect0
      | raw_ident_list_rect_arrow0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_list_rect_arrow0
      | raw_ident_eager_list_rect_arrow0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0
            raw_ident_eager_list_rect_arrow0
      | raw_ident_List_nth_default0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_List_nth_default0
      | raw_ident_eager_List_nth_default0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0
            raw_ident_eager_List_nth_default0
      end .
Admitted.
Definition invert_bind_args_unknown0 :
    forall (t : type.type (base.type.type base)) (_ : ident t)
      (pidc : raw_ident),
    option
      match pidc return Type with
      | raw_ident_false0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_false0
      | raw_ident_flat_map =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_flat_map
      | raw_ident_app =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_app
      | raw_ident_map =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_map
      | raw_ident_snd =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_snd
      | raw_ident_fst =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_fst
      | raw_ident_Z0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_Z0
      | raw_ident_add =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_add
      | raw_ident_literal0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_literal0
      | raw_ident_nil0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_nil0
      | raw_ident_cons0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_cons0
      | raw_ident_Some0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_Some0
      | raw_ident_None0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_None0
      | raw_ident_pair0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_pair0
      | raw_ident_tt0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_tt0
      | raw_ident_prod_rect_nodep0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_prod_rect_nodep0
      | raw_ident_bool_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_bool_rect0
      | raw_ident_list_case0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_list_case0
      | raw_ident_option_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_option_rect0
      | raw_ident_nat_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_nat_rect0
      | raw_ident_eager_nat_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_eager_nat_rect0
      | raw_ident_nat_rect_arrow0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_nat_rect_arrow0
      | raw_ident_eager_nat_rect_arrow0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0
            raw_ident_eager_nat_rect_arrow0
      | raw_ident_list_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_list_rect0
      | raw_ident_eager_list_rect0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_eager_list_rect0
      | raw_ident_list_rect_arrow0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_list_rect_arrow0
      | raw_ident_eager_list_rect_arrow0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0
            raw_ident_eager_list_rect_arrow0
      | raw_ident_List_nth_default0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0 raw_ident_List_nth_default0
      | raw_ident_eager_List_nth_default0 =>
          @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types base
            ident raw_ident raw_ident_infos_of0
            raw_ident_eager_List_nth_default0
      end .
Admitted.
Definition all_pattern_idents0 :
    list (@PrimitiveSigma.Primitive.sigT Type (fun T : Type => T)) .
Admitted.
Definition eta_ident_cps_gen4 :
    forall
      (T : forall (t : type.type (pattern.base.type.type base))
             (_ : pattern_ident t), Type)
      (f : forall (t : type.type (pattern.base.type.type base))
             (idc : pattern_ident t), T t idc),
    @sig
      (forall (t : type.type (pattern.base.type.type base))
         (idc : pattern_ident t), T t idc)
      (fun
         f' : forall (t : type.type (pattern.base.type.type base))
                (idc : pattern_ident t), T t idc =>
       forall (t : type.type (pattern.base.type.type base))
         (idc : pattern_ident t), @eq (T t idc) (f' t idc) (f t idc)) .
Admitted.
Definition eta_ident_cps_gen_expand_literal2 :
    forall
      (T : forall (t : type.type (pattern.base.type.type base))
             (_ : pattern_ident t), Type)
      (f : forall (t : type.type (pattern.base.type.type base))
             (idc : pattern_ident t), T t idc),
    @sig
      (forall (t : type.type (pattern.base.type.type base))
         (idc : pattern_ident t), T t idc)
      (fun
         f' : forall (t : type.type (pattern.base.type.type base))
                (idc : pattern_ident t), T t idc =>
       forall (t : type.type (pattern.base.type.type base))
         (idc : pattern_ident t), @eq (T t idc) (f' t idc) (f t idc)) .
Admitted.
Definition split_types0 :
    forall (t : type.type (pattern.base.type.type base))
      (_ : pattern_ident t),
    @PrimitiveSigma.Primitive.sigT raw_ident
      (fun ridc : raw_ident =>
       prod
         (@fold_right Type Type (fun A B : Type => prod A B) unit
            (@IdentifiersLibrary.Compilers.pattern.Raw.ident.dep_types _ _
               (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _ _
                  (raw_ident_infos_of0 ridc))))
         (@fold_right Type Type (fun A B : Type => prod A B) unit
            (@map IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
               Type
               (IdentifiersLibrary.Compilers.pattern.ident.Type_of_kind_of_type
                  base)
               (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types _
                  _
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                     _ (raw_ident_infos_of0 ridc)))))) .
Admitted.
Definition add_types_from_raw_sig0 :
    forall (ridc : raw_ident)
      (dt : @fold_right Type Type (fun A B : Type => prod A B) unit
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.dep_types _ _
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 ridc))))
      (idt : @fold_right Type Type (fun A B : Type => prod A B) unit
               (@map
                  IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                  Type
                  (IdentifiersLibrary.Compilers.pattern.ident.Type_of_kind_of_type
                     base)
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                     _ _
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                        _ _ (raw_ident_infos_of0 ridc))))),
    @PrimitiveSigma.Primitive.sigT (type.type (pattern.base.type.type base))
      (fun t : type.type (pattern.base.type.type base) =>
       @sig (pattern_ident t)
         (fun idc : pattern_ident t =>
          @eq
            (@PrimitiveSigma.Primitive.sigT raw_ident
               (fun ridc0 : raw_ident =>
                prod
                  (@fold_right Type Type (fun A B : Type => prod A B) unit
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.dep_types
                        _ _
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                           _ _ (raw_ident_infos_of0 ridc0))))
                  (@fold_right Type Type (fun A B : Type => prod A B) unit
                     (@map
                        IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                        Type
                        (IdentifiersLibrary.Compilers.pattern.ident.Type_of_kind_of_type
                           base)
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                           _ _
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                              _ _ (raw_ident_infos_of0 ridc0)))))))
            (split_types0 t idc)
            (@PrimitiveSigma.Primitive.existT raw_ident
               (fun ridc0 : raw_ident =>
                prod
                  (@fold_right Type Type (fun A B : Type => prod A B) unit
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.dep_types
                        _ _
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                           _ _ (raw_ident_infos_of0 ridc0))))
                  (@fold_right Type Type (fun A B : Type => prod A B) unit
                     (@map
                        IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                        Type
                        (IdentifiersLibrary.Compilers.pattern.ident.Type_of_kind_of_type
                           base)
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                           _ _
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                              _ _ (raw_ident_infos_of0 ridc0)))))) ridc
               (@pair
                  (@fold_right Type Type (fun A B : Type => prod A B) unit
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.dep_types
                        _ _
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                           _ _ (raw_ident_infos_of0 ridc))))
                  (@fold_right Type Type (fun A B : Type => prod A B) unit
                     (@map
                        IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                        Type
                        (IdentifiersLibrary.Compilers.pattern.ident.Type_of_kind_of_type
                           base)
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                           _ _
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                              _ _ (raw_ident_infos_of0 ridc))))) dt idt)))).
Admitted.
Definition to_type_split_types_subst_default_eq0 :
    forall (t : type.type (pattern.base.type.type base))
      (idc : pattern_ident t)
      (evm : FMapPositive.PositiveMap.t (base.type.type base)),
    @eq (type.type (base.type.type base))
      (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type _ _
         (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _ _
            (raw_ident_infos_of0
               (@PrimitiveSigma.Primitive.projT1 _ _
                  (@IdentifiersLibrary.Compilers.pattern.ident.split_types_subst_default
                     base ident raw_ident raw_ident_infos_of0 pattern_ident
                     split_types0 t idc evm))))
         (@fst
            (@fold_right Type Type (fun A B : Type => prod A B) unit
               (@IdentifiersLibrary.Compilers.pattern.Raw.ident.dep_types _ _
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                     _
                     (raw_ident_infos_of0
                        (@PrimitiveSigma.Primitive.projT1 _ _
                           (@IdentifiersLibrary.Compilers.pattern.ident.split_types_subst_default
                              base ident raw_ident raw_ident_infos_of0
                              pattern_ident split_types0 t idc evm))))))
            (@fold_right Type Type (fun A B : Type => prod A B) unit
               (@map
                  IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                  Type
                  (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                     base)
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                     _ _
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                        _ _
                        (raw_ident_infos_of0
                           (@PrimitiveSigma.Primitive.projT1 _ _
                              (@IdentifiersLibrary.Compilers.pattern.ident.split_types_subst_default
                                 base ident raw_ident raw_ident_infos_of0
                                 pattern_ident split_types0 t idc evm)))))))
            (@PrimitiveSigma.Primitive.projT2 _ _
               (@IdentifiersLibrary.Compilers.pattern.ident.split_types_subst_default
                  base ident raw_ident raw_ident_infos_of0 pattern_ident
                  split_types0 t idc evm)))
         (@snd
            (@fold_right Type Type (fun A B : Type => prod A B) unit
               (@IdentifiersLibrary.Compilers.pattern.Raw.ident.dep_types _ _
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                     _
                     (raw_ident_infos_of0
                        (@PrimitiveSigma.Primitive.projT1 _ _
                           (@IdentifiersLibrary.Compilers.pattern.ident.split_types_subst_default
                              base ident raw_ident raw_ident_infos_of0
                              pattern_ident split_types0 t idc evm))))))
            (@fold_right Type Type (fun A B : Type => prod A B) unit
               (@map
                  IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                  Type
                  (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                     base)
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                     _ _
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                        _ _
                        (raw_ident_infos_of0
                           (@PrimitiveSigma.Primitive.projT1 _ _
                              (@IdentifiersLibrary.Compilers.pattern.ident.split_types_subst_default
                                 base ident raw_ident raw_ident_infos_of0
                                 pattern_ident split_types0 t idc evm)))))))
            (@PrimitiveSigma.Primitive.projT2 _ _
               (@IdentifiersLibrary.Compilers.pattern.ident.split_types_subst_default
                  base ident raw_ident raw_ident_infos_of0 pattern_ident
                  split_types0 t idc evm))))
      (@IdentifiersLibrary.Compilers.pattern.type.subst_default base t evm).
Admitted.
Definition projT1_add_types_from_raw_sig_eq0 :
    forall (t : type.type (base.type.type base)) (idc : ident t),
    @eq (type.type (pattern.base.type.type base))
      (@PrimitiveSigma.Primitive.projT1 _ _
         (add_types_from_raw_sig0
            (@PrimitiveSigma.Primitive.projT1 _ _
               (split_raw_ident_gen0 t idc))
            (@PrimitiveSigma.Primitive.projT1 _ _
               (@proj1_sig
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                     base ident
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                        _ _
                        (raw_ident_infos_of0
                           (@PrimitiveSigma.Primitive.projT1 _ _
                              (split_raw_ident_gen0 t idc)))))
                  (fun
                     args : @IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                              base ident
                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                 _ _
                                 (raw_ident_infos_of0
                                    (@PrimitiveSigma.Primitive.projT1 _ _
                                       (split_raw_ident_gen0 t idc)))) =>
                   @sig
                     (@eq (type.type (base.type.type base))
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                           _ _
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                              _ _
                              (raw_ident_infos_of0
                                 (@PrimitiveSigma.Primitive.projT1 _ _
                                    (split_raw_ident_gen0 t idc))))
                           (@PrimitiveSigma.Primitive.projT1 _ _ args)
                           (@fst
                              (@fold_right Type Type
                                 (fun A B : Type => prod A B) unit
                                 (@map
                                    IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                    Type
                                    (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                       base)
                                    (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                       _ _
                                       (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                          _ _
                                          (raw_ident_infos_of0
                                             (@PrimitiveSigma.Primitive.projT1
                                                _ _
                                                (split_raw_ident_gen0 t idc)))))))
                              (@fold_right Type Type
                                 (fun A B : Type => prod A B) unit
                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                    _ _
                                    (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                       _ _
                                       (raw_ident_infos_of0
                                          (@PrimitiveSigma.Primitive.projT1 _
                                             _ (split_raw_ident_gen0 t idc))))
                                    (@PrimitiveSigma.Primitive.projT1 _ _
                                       args)))
                              (@PrimitiveSigma.Primitive.projT2 _ _ args))) t)
                     (fun
                        pf : @eq (type.type (base.type.type base))
                               (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                                  _ _
                                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                     _ _
                                     (raw_ident_infos_of0
                                        (@PrimitiveSigma.Primitive.projT1 _ _
                                           (split_raw_ident_gen0 t idc))))
                                  (@PrimitiveSigma.Primitive.projT1 _ _ args)
                                  (@fst
                                     (@fold_right Type Type
                                        (fun A B : Type => prod A B) unit
                                        (@map
                                           IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                           Type
                                           (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                              base)
                                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                              _ _
                                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc)))))))
                                     (@fold_right Type Type
                                        (fun A B : Type => prod A B) unit
                                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                           _ _
                                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                              _ _
                                              (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                           (@PrimitiveSigma.Primitive.projT1
                                              _ _ args)))
                                     (@PrimitiveSigma.Primitive.projT2 _ _
                                        args))) t =>
                      @eq (ident t) idc
                        (@eq_rect (type.type (base.type.type base))
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                              _ _
                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                 _ _
                                 (raw_ident_infos_of0
                                    (@PrimitiveSigma.Primitive.projT1 _ _
                                       (split_raw_ident_gen0 t idc))))
                              (@PrimitiveSigma.Primitive.projT1 _ _ args)
                              (@fst
                                 (@fold_right Type Type
                                    (fun A B : Type => prod A B) unit
                                    (@map
                                       IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                       Type
                                       (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                          base)
                                       (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                          _ _
                                          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                             _ _
                                             (raw_ident_infos_of0
                                                (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc)))))))
                                 (@fold_right Type Type
                                    (fun A B : Type => prod A B) unit
                                    (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                       _ _
                                       (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                          _ _
                                          (raw_ident_infos_of0
                                             (@PrimitiveSigma.Primitive.projT1
                                                _ _
                                                (split_raw_ident_gen0 t idc))))
                                       (@PrimitiveSigma.Primitive.projT1 _ _
                                          args)))
                                 (@PrimitiveSigma.Primitive.projT2 _ _ args)))
                           ident
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.assemble_ident
                              base ident
                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                 _ _
                                 (raw_ident_infos_of0
                                    (@PrimitiveSigma.Primitive.projT1 _ _
                                       (split_raw_ident_gen0 t idc)))) args)
                           t pf)))
                  (@PrimitiveSigma.Primitive.projT2 _ _
                     (split_raw_ident_gen0 t idc))))
            (@IdentifiersLibrary.Compilers.lift_type_of_list_map
               IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
               (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types _
                  _
                  (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                     _
                     (raw_ident_infos_of0
                        (@PrimitiveSigma.Primitive.projT1 _ _
                           (split_raw_ident_gen0 t idc)))))
               (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                  base)
               (IdentifiersLibrary.Compilers.pattern.ident.Type_of_kind_of_type
                  base)
               (@IdentifiersLibrary.Compilers.pattern.ident.relax_kind_of_type
                  base)
               (@fst
                  (@fold_right Type Type (fun A B : Type => prod A B) unit
                     (@map
                        IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                        Type
                        (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                           base)
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                           _ _
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                              _ _
                              (raw_ident_infos_of0
                                 (@PrimitiveSigma.Primitive.projT1 _ _
                                    (split_raw_ident_gen0 t idc)))))))
                  (@fold_right Type Type (fun A B : Type => prod A B) unit
                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                        _ _
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                           _ _
                           (raw_ident_infos_of0
                              (@PrimitiveSigma.Primitive.projT1 _ _
                                 (split_raw_ident_gen0 t idc))))
                        (@PrimitiveSigma.Primitive.projT1 _ _
                           (@proj1_sig
                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                                 base ident
                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                    _ _
                                    (raw_ident_infos_of0
                                       (@PrimitiveSigma.Primitive.projT1 _ _
                                          (split_raw_ident_gen0 t idc)))))
                              (fun
                                 args : @IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                                          base ident
                                          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                             _ _
                                             (raw_ident_infos_of0
                                                (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                               =>
                               @sig
                                 (@eq (type.type (base.type.type base))
                                    (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                                       _ _
                                       (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                          _ _
                                          (raw_ident_infos_of0
                                             (@PrimitiveSigma.Primitive.projT1
                                                _ _
                                                (split_raw_ident_gen0 t idc))))
                                       (@PrimitiveSigma.Primitive.projT1 _ _
                                          args)
                                       (@fst
                                          (@fold_right Type Type
                                             (fun A B : Type => prod A B)
                                             unit
                                             (@map
                                                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                                Type
                                                (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                                 base)
                                                (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                                 _ _
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc)))))))
                                          (@fold_right Type Type
                                             (fun A B : Type => prod A B)
                                             unit
                                             (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                                _ _
                                                (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                                (@PrimitiveSigma.Primitive.projT1
                                                 _ _ args)))
                                          (@PrimitiveSigma.Primitive.projT2 _
                                             _ args))) t)
                                 (fun
                                    pf : @eq
                                           (type.type (base.type.type base))
                                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                                              _ _
                                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                              (@PrimitiveSigma.Primitive.projT1
                                                 _ _ args)
                                              (@fst
                                                 (@fold_right Type Type
                                                 (fun A B : Type => prod A B)
                                                 unit
                                                 (@map
                                                 IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                                 Type
                                                 (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                                 base)
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                                 _ _
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc)))))))
                                                 (@fold_right Type Type
                                                 (fun A B : Type => prod A B)
                                                 unit
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                                 _ _
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _ args)))
                                                 (@PrimitiveSigma.Primitive.projT2
                                                 _ _ args))) t =>
                                  @eq (ident t) idc
                                    (@eq_rect
                                       (type.type (base.type.type base))
                                       (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                                          _ _
                                          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                             _ _
                                             (raw_ident_infos_of0
                                                (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                          (@PrimitiveSigma.Primitive.projT1 _
                                             _ args)
                                          (@fst
                                             (@fold_right Type Type
                                                (fun A B : Type => prod A B)
                                                unit
                                                (@map
                                                 IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                                 Type
                                                 (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                                 base)
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                                 _ _
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc)))))))
                                             (@fold_right Type Type
                                                (fun A B : Type => prod A B)
                                                unit
                                                (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                                 _ _
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _ args)))
                                             (@PrimitiveSigma.Primitive.projT2
                                                _ _ args))) ident
                                       (@IdentifiersLibrary.Compilers.pattern.Raw.ident.assemble_ident
                                          base ident
                                          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                             _ _
                                             (raw_ident_infos_of0
                                                (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                          args) t pf)))
                              (@PrimitiveSigma.Primitive.projT2 _ _
                                 (split_raw_ident_gen0 t idc))))))
                  (@PrimitiveSigma.Primitive.projT2 _ _
                     (@proj1_sig
                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                           base ident
                           (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                              _ _
                              (raw_ident_infos_of0
                                 (@PrimitiveSigma.Primitive.projT1 _ _
                                    (split_raw_ident_gen0 t idc)))))
                        (fun
                           args : @IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                                    base ident
                                    (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                       _ _
                                       (raw_ident_infos_of0
                                          (@PrimitiveSigma.Primitive.projT1 _
                                             _ (split_raw_ident_gen0 t idc))))
                         =>
                         @sig
                           (@eq (type.type (base.type.type base))
                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                                 _ _
                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                    _ _
                                    (raw_ident_infos_of0
                                       (@PrimitiveSigma.Primitive.projT1 _ _
                                          (split_raw_ident_gen0 t idc))))
                                 (@PrimitiveSigma.Primitive.projT1 _ _ args)
                                 (@fst
                                    (@fold_right Type Type
                                       (fun A B : Type => prod A B) unit
                                       (@map
                                          IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                          Type
                                          (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                             base)
                                          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                             _ _
                                             (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                _ _
                                                (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc)))))))
                                    (@fold_right Type Type
                                       (fun A B : Type => prod A B) unit
                                       (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                          _ _
                                          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                             _ _
                                             (raw_ident_infos_of0
                                                (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                          (@PrimitiveSigma.Primitive.projT1 _
                                             _ args)))
                                    (@PrimitiveSigma.Primitive.projT2 _ _
                                       args))) t)
                           (fun
                              pf : @eq (type.type (base.type.type base))
                                     (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                                        _ _
                                        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                           _ _
                                           (raw_ident_infos_of0
                                              (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                        (@PrimitiveSigma.Primitive.projT1 _ _
                                           args)
                                        (@fst
                                           (@fold_right Type Type
                                              (fun A B : Type => prod A B)
                                              unit
                                              (@map
                                                 IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                                 Type
                                                 (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                                 base)
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                                 _ _
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc)))))))
                                           (@fold_right Type Type
                                              (fun A B : Type => prod A B)
                                              unit
                                              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                                 _ _
                                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _ args)))
                                           (@PrimitiveSigma.Primitive.projT2
                                              _ _ args))) t =>
                            @eq (ident t) idc
                              (@eq_rect (type.type (base.type.type base))
                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_type
                                    _ _
                                    (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                       _ _
                                       (raw_ident_infos_of0
                                          (@PrimitiveSigma.Primitive.projT1 _
                                             _ (split_raw_ident_gen0 t idc))))
                                    (@PrimitiveSigma.Primitive.projT1 _ _
                                       args)
                                    (@fst
                                       (@fold_right Type Type
                                          (fun A B : Type => prod A B) unit
                                          (@map
                                             IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                                             Type
                                             (IdentifiersLibrary.Compilers.pattern.Raw.ident.Type_of_kind_of_type
                                                base)
                                             (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_types
                                                _ _
                                                (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                 _ _
                                                 (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc)))))))
                                       (@fold_right Type Type
                                          (fun A B : Type => prod A B) unit
                                          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.indep_args
                                             _ _
                                             (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                                _ _
                                                (raw_ident_infos_of0
                                                 (@PrimitiveSigma.Primitive.projT1
                                                 _ _
                                                 (split_raw_ident_gen0 t idc))))
                                             (@PrimitiveSigma.Primitive.projT1
                                                _ _ args)))
                                       (@PrimitiveSigma.Primitive.projT2 _ _
                                          args))) ident
                                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.assemble_ident
                                    base ident
                                    (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos
                                       _ _
                                       (raw_ident_infos_of0
                                          (@PrimitiveSigma.Primitive.projT1 _
                                             _ (split_raw_ident_gen0 t idc))))
                                    args) t pf)))
                        (@PrimitiveSigma.Primitive.projT2 _ _
                           (split_raw_ident_gen0 t idc))))))))
      (@IdentifiersLibrary.Compilers.pattern.type.relax base t).
Admitted.
Definition arg_types_unfolded0 :
    forall (t : type.type (pattern.base.type.type base))
      (_ : pattern_ident t), list Type.
exact (fun (t : type.type (pattern.base.type.type base)) (idc : pattern_ident t)
    =>
    match idc in (pattern_ident t0) return (list Type) with
    | pattern_ident_false0 => @nil Type
    | pattern_ident_flat_map _ _ => @nil Type
    | pattern_ident_app _ => @nil Type
    | pattern_ident_map _ _ => @nil Type
    | pattern_ident_snd _ _ => @nil Type
    | pattern_ident_fst _ _ => @nil Type
    | pattern_ident_Z0 => @nil Type
    | pattern_ident_add => @nil Type
    | pattern_ident_literal0 t0 =>
        @cons Type
          match t0 return Type with
          | base_Z => Z
          | base_nat0 => nat
          | base_bool0 => bool
          end (@nil Type)
    | pattern_ident_nil0 _ => @nil Type
    | pattern_ident_cons0 _ => @nil Type
    | pattern_ident_Some0 _ => @nil Type
    | pattern_ident_None0 _ => @nil Type
    | pattern_ident_pair0 _ _ => @nil Type
    | pattern_ident_tt0 => @nil Type
    | pattern_ident_prod_rect_nodep0 _ _ _ => @nil Type
    | pattern_ident_bool_rect0 _ => @nil Type
    | pattern_ident_list_case0 _ _ => @nil Type
    | pattern_ident_option_rect0 _ _ => @nil Type
    | pattern_ident_nat_rect0 _ => @nil Type
    | pattern_ident_eager_nat_rect0 _ => @nil Type
    | pattern_ident_nat_rect_arrow0 _ _ => @nil Type
    | pattern_ident_eager_nat_rect_arrow0 _ _ => @nil Type
    | pattern_ident_list_rect0 _ _ => @nil Type
    | pattern_ident_eager_list_rect0 _ _ => @nil Type
    | pattern_ident_list_rect_arrow0 _ _ _ => @nil Type
    | pattern_ident_eager_list_rect_arrow0 _ _ _ => @nil Type
    | pattern_ident_List_nth_default0 _ => @nil Type
    | pattern_ident_eager_List_nth_default0 _ => @nil Type
    end).
Defined.
Definition type_of_list_arg_types_beq_unfolded0 :
    forall (t : type.type (pattern.base.type.type base))
      (idc : pattern_ident t)
      (_ : @fold_right Type Type (fun A B : Type => prod A B) unit
             (arg_types_unfolded0 t idc))
      (_ : @fold_right Type Type (fun A B : Type => prod A B) unit
             (arg_types_unfolded0 t idc)), bool.
admit.
Defined.
Definition to_typed_unfolded0 :
    forall (t : type.type (pattern.base.type.type base))
      (idc : pattern_ident t)
      (evm : FMapPositive.PositiveMap.tree (base.type.type base))
      (_ : @fold_right Type Type (fun A B : Type => prod A B) unit
             (arg_types_unfolded0 t idc)),
    ident
      (@IdentifiersLibrary.Compilers.pattern.type.subst_default base t evm).
Admitted.
Definition of_typed_ident_unfolded0 :
    forall (t : type.type (base.type.type base)) (_ : ident t),
    pattern_ident (@IdentifiersLibrary.Compilers.pattern.type.relax base t).
exact (fun (t : type.type (base.type.type base)) (idc : ident t) =>
    match
      idc in (ident t0)
      return
        (pattern_ident
           (@IdentifiersLibrary.Compilers.pattern.type.relax base t0))
    with
    | ident_false0 => pattern_ident_false0
    | ident_flat_map t0 t1 =>
        pattern_ident_flat_map
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_app t0 =>
        pattern_ident_app
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_map t0 t1 =>
        pattern_ident_map
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_snd t0 t1 =>
        pattern_ident_snd
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_fst t0 t1 =>
        pattern_ident_fst
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_Z0 => pattern_ident_Z0
    | ident_add => pattern_ident_add
    | ident_literal0 t0 _ => pattern_ident_literal0 t0
    | ident_nil0 t0 =>
        pattern_ident_nil0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_cons0 t0 =>
        pattern_ident_cons0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_Some0 t0 =>
        pattern_ident_Some0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_None0 t0 =>
        pattern_ident_None0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_pair0 t0 t1 =>
        pattern_ident_pair0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_tt0 => pattern_ident_tt0
    | ident_prod_rect_nodep0 t0 t1 t2 =>
        pattern_ident_prod_rect_nodep0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t2)
    | ident_bool_rect0 t0 =>
        pattern_ident_bool_rect0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_list_case0 t0 t1 =>
        pattern_ident_list_case0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_option_rect0 t0 t1 =>
        pattern_ident_option_rect0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_nat_rect0 t0 =>
        pattern_ident_nat_rect0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_eager_nat_rect0 t0 =>
        pattern_ident_eager_nat_rect0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_nat_rect_arrow0 t0 t1 =>
        pattern_ident_nat_rect_arrow0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_eager_nat_rect_arrow0 t0 t1 =>
        pattern_ident_eager_nat_rect_arrow0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_list_rect0 t0 t1 =>
        pattern_ident_list_rect0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_eager_list_rect0 t0 t1 =>
        pattern_ident_eager_list_rect0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
    | ident_list_rect_arrow0 t0 t1 t2 =>
        pattern_ident_list_rect_arrow0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t2)
    | ident_eager_list_rect_arrow0 t0 t1 t2 =>
        pattern_ident_eager_list_rect_arrow0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t1)
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t2)
    | ident_List_nth_default0 t0 =>
        pattern_ident_List_nth_default0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    | ident_eager_List_nth_default0 t0 =>
        pattern_ident_eager_List_nth_default0
          (@IdentifiersLibrary.Compilers.pattern.base.relax base t0)
    end).
Defined.
Definition arg_types_of_typed_ident_unfolded0 :
    forall (t : type.type (base.type.type base)) (idc : ident t),
    @fold_right Type Type (fun A B : Type => prod A B) unit
      (arg_types_unfolded0
         (@IdentifiersLibrary.Compilers.pattern.type.relax base t)
         (of_typed_ident_unfolded0 t idc)).
admit.
Defined.
Definition unify0 :
    forall (t : type.type (pattern.base.type.type base))
      (t' : type.type (base.type.type base)) (pidc : pattern_ident t)
      (_ : ident t'),
    option
      (@fold_right Type Type (fun A B : Type => prod A B) unit
         (@IdentifiersLibrary.Compilers.pattern.ident.arg_types base ident
            raw_ident raw_ident_infos_of0 pattern_ident eta_ident_cps_gen4
            split_types0 t pidc)).
Admitted.
Definition unify_unknown0 :
    forall (t : type.type (pattern.base.type.type base))
      (t' : type.type (base.type.type base)) (pidc : pattern_ident t)
      (_ : ident t'),
    option
      (@fold_right Type Type (fun A B : Type => prod A B) unit
         (@IdentifiersLibrary.Compilers.pattern.ident.arg_types base ident
            raw_ident raw_ident_infos_of0 pattern_ident eta_ident_cps_gen4
            split_types0 t pidc)).
Admitted.
Notation reify_package   :=
      (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprReifyInfo
        (IdentifiersBasicLibrary.Compilers.Basic.GoalType.Build_package
           (Classes.Build_ExprInfoT base ident base_interp0 ident_interp0)
           (Classes.Build_ExprExtraInfoT
              (Classes.Build_ExprInfoT base ident base_interp0 ident_interp0)
              base_beq0 base_interp_beq0 try_make_base_transport_cps0
              baseHasNat0 buildIdent0 toRestrictedIdent0 buildEagerIdent0
              invertIdent0 base_default0 reflect_base_beq0
              reflect_base_interp_beq0 try_make_base_transport_cps_correct0
              baseHasNatCorrect0 toFromRestrictedIdent0
              buildInvertIdentCorrect0 buildInterpIdentCorrect0
              buildInterpEagerIdentCorrect0 ident_interp_Proper0)
           (IdentifiersBasicLibrary.Compilers.Basic.GoalType.Build_ExprReifyInfoT
              (Classes.Build_ExprInfoT base ident base_interp0 ident_interp0)
              all_base_and_interp0 all_ident_and_interp0) ident_is_var_like0)).
Notation exprInfo   :=
      (Classes.Build_ExprInfoT base ident base_interp0 ident_interp0).
Notation exprExtraInfo   :=
      (Classes.Build_ExprExtraInfoT
        (Classes.Build_ExprInfoT base ident base_interp0 ident_interp0)
        base_beq0 base_interp_beq0 try_make_base_transport_cps0 baseHasNat0
        buildIdent0 toRestrictedIdent0 buildEagerIdent0 invertIdent0
        base_default0 reflect_base_beq0 reflect_base_interp_beq0
        try_make_base_transport_cps_correct0 baseHasNatCorrect0
        toFromRestrictedIdent0 buildInvertIdentCorrect0
        buildInterpIdentCorrect0 buildInterpEagerIdentCorrect0
        ident_interp_Proper0).
Notation pkg   :=
      (IdentifiersLibrary.Compilers.pattern.ident.GoalType.Build_package base
        ident all_base2 all_idents2 ident_index1 eta_ident_cps_gen2
        eta_ident_cps_gen_expand_literal1 eta_ident_cps0 simple_idents0
        raw_ident all_raw_idents0 ident_index2 raw_ident_index_idempotent0
        eta_ident_cps_gen3 raw_ident_infos_of0 split_raw_ident_gen0
        raw_invert_bind_args0 invert_bind_args_unknown0 pattern_ident
        all_pattern_idents0 eta_ident_cps_gen4
        eta_ident_cps_gen_expand_literal2 split_types0
        add_types_from_raw_sig0 to_type_split_types_subst_default_eq0
        projT1_add_types_from_raw_sig_eq0 arg_types_unfolded0
        to_typed_unfolded0 type_of_list_arg_types_beq_unfolded0
        of_typed_ident_unfolded0 arg_types_of_typed_ident_unfolded0 unify0
        unify_unknown0).
Notation ident_is_var_like   :=
      ident_is_var_like0.
Notation include_interp   := false.
Notation specs   :=
      (@cons (prod bool Prop)
        (@pair bool Prop false (forall n : Z, @eq Z (Z.add n Z0) n))
        (@cons (prod bool Prop)
           (@pair bool Prop false
              (forall (A B : Type) (a : A) (b : B),
               @eq A (@fst A B (@pair A B a b)) a))
           (@cons (prod bool Prop)
              (@pair bool Prop false
                 (forall (A B : Type) (a : A) (b : B),
                  @eq B (@snd A B (@pair A B a b)) b))
              (@cons (prod bool Prop)
                 (@pair bool Prop false
                    (forall (A B : Type) (f : forall _ : A, B) (ls : list A),
                     @eq (list B) (@map A B f ls)
                       (@ident.eagerly
                          (forall (A0 : Type) (P : forall _ : list A0, Type)
                             (_ : P (@nil A0))
                             (_ : forall (a : A0) (l : list A0) (_ : P l),
                                  P (@cons A0 a l))
                             (l : list A0), P l) list_rect A
                          (fun _ : list A => list B)
                          (@nil B)
                          (fun (x : A) (_ : list A) (map_f_xs : list B) =>
                           @cons B (f x) map_f_xs) ls)))
                 (@cons (prod bool Prop)
                    (@pair bool Prop false
                       (forall (A : Type) (xs ys : list A),
                        @eq (list A) (@app A xs ys)
                          (@ident.eagerly
                             (forall (A0 : Type)
                                (P : forall _ : list A0, Type)
                                (_ : P (@nil A0))
                                (_ : forall (a : A0) (l : list A0) (_ : P l),
                                     P (@cons A0 a l))
                                (l : list A0), P l) list_rect A
                             (fun _ : list A => list A) ys
                             (fun (x : A) (_ app_xs_ys : list A) =>
                              @cons A x app_xs_ys) xs)))
                    (@cons (prod bool Prop)
                       (@pair bool Prop false
                          (forall (A P Q : Type) (N : forall _ : P, Q)
                             (C : forall (_ : A) (_ : list A)
                                    (_ : forall _ : P, Q)
                                    (_ : P), Q) (ls : list A)
                             (v : P),
                           @eq Q (@list_rect_arrow_nodep A P Q N C ls v)
                             (@ident.eagerly
                                (forall (A0 P0 Q0 : Type)
                                   (_ : forall _ : P0, Q0)
                                   (_ : forall (_ : A0)
                                          (_ : list A0)
                                          (_ : forall _ : P0, Q0)
                                          (_ : P0), Q0)
                                   (_ : list A0) (_ : P0), Q0)
                                (@list_rect_arrow_nodep) A P Q N C ls v)))
                       (@cons (prod bool Prop)
                          (@pair bool Prop false
                             (forall (A P : Type)
                                (N : forall _ : unit, P)
                                (C : forall (_ : A) (_ : list A) (_ : P), P)
                                (ls : list A),
                              @eq P (@Thunked.list_rect A P N C ls)
                                (@ident.eagerly
                                   (forall (A0 P0 : Type)
                                      (_ : forall _ : unit, P0)
                                      (_ : forall
                                             (_ : A0)
                                             (_ : list A0)
                                             (_ : P0), P0)
                                      (_ : list A0), P0)
                                   (@Thunked.list_rect) A P N C ls)))
                          (@cons (prod bool Prop)
                             (@pair bool Prop false
                                (forall (A P : Type)
                                   (N : forall _ : unit, P)
                                   (C : forall (_ : A) (_ : list A), P),
                                 @eq P (@Thunked.list_case A P N C (@nil A))
                                   (N tt)))
                             (@cons (prod bool Prop)
                                (@pair bool Prop false
                                   (forall (A P : Type)
                                      (N : forall _ : unit, P)
                                      (C : forall (_ : A) (_ : list A), P)
                                      (x : A) (xs : list A),
                                    @eq P
                                      (@Thunked.list_case A P N C
                                         (@cons A x xs))
                                      (C x xs)))
                                (@cons (prod bool Prop)
                                   (@pair bool Prop false
                                      (forall (A : Type)
                                         (default : A)
                                         (ls : list A)
                                         (n : nat),
                                       @eq A
                                         (@nth_default A default ls
                                            (@ident.literal nat n))
                                         (@ident.eagerly
                                            (forall
                                               (A0 : Type)
                                               (_ : A0)
                                               (_ : list A0)
                                               (_ : nat), A0) nth_default A
                                            default ls
                                            (@ident.literal nat n))))
                                   (@cons (prod bool Prop)
                                      (@pair bool Prop true
                                         (forall (A B : Type)
                                            (f : forall _ : A, list B)
                                            (xs : list A),
                                          @eq (list B)
                                            (@flat_map A B f xs)
                                            (@list_rect A
                                               (fun _ : list A => list B)
                                               (@nil B)
                                               (fun
                                                 (x : A)
                                                 (_ : list A)
                                                 (flat_map_tl : list B) =>
                                                @app B (f x) flat_map_tl) xs)))
                                      (@nil (prod bool Prop))))))))))))).

  Goal ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args
       scraped_data InductiveHList.nil base ident raw_ident pattern_ident   false   false   true rules_proofs.

    Unset Ltac Backtrace.
    Set Printing All.
    Set Printing Depth 100000000.
    let reify_package := constr:(reify_package) in
    let exprInfo := constr:(exprInfo) in
    let exprExtraInfo := constr:(exprExtraInfo) in
    let pkg := constr:(pkg) in
    let ident_is_var_like := constr:(ident_is_var_like) in
    let include_interp := constr:(include_interp) in
    let specs := constr:(specs) in
    let reify_base :=
    IdentifiersBasicGenerate.Compilers.Basic.Tactic.reify_base_via_reify_package
     reify_package
   in
   let reify_ident :=
    IdentifiersBasicGenerate.Compilers.Basic.Tactic.reify_ident_via_reify_package
     reify_package
   in
   let v := Reify.Compilers.RewriteRules.Make.Reify reify_base reify_ident exprInfo
                                                    exprExtraInfo pkg ident_is_var_like include_interp specs in
   idtac v.

