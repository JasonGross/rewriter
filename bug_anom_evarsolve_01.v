(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+undeclared-scope,+deprecated-typeclasses-transparency-without-locality,unsupported-attributes" "-R" "src/Rewriter" "Rewriter" "-I" "src/Rewriter/Util/plugins" "-top" "Rewriter.Rewriter.Examples" "-native-compiler" "ondemand" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2055 lines to 1411 lines, then from 1424 lines to 1327 lines, then from 1340 lines to 1498 lines, then from 1503 lines to 1328 lines, then from 1341 lines to 1508 lines, then from 1513 lines to 1330 lines, then from 1343 lines to 1501 lines, then from 1506 lines to 1333 lines, then from 1346 lines to 1502 lines, then from 1507 lines to 1366 lines, then from 1379 lines to 5401 lines, then from 5404 lines to 1415 lines, then from 1428 lines to 2841 lines, then from 2844 lines to 2214 lines, then from 2227 lines to 2256 lines, then from 2261 lines to 2221 lines, then from 2234 lines to 4165 lines, then from 4168 lines to 3564 lines, then from 3578 lines to 3618 lines, then from 3624 lines to 3581 lines, then from 3595 lines to 3618 lines, then from 3624 lines to 3581 lines, then from 3595 lines to 4591 lines, then from 4597 lines to 4298 lines, then from 4312 lines to 4353 lines, then from 4359 lines to 4308 lines, then from 4322 lines to 4356 lines, then from 4362 lines to 4321 lines, then from 4335 lines to 4375 lines, then from 4381 lines to 4338 lines, then from 4352 lines to 4384 lines, then from 4390 lines to 4475 lines *)
(* coqc version 8.15.0 compiled with OCaml 4.11.2
   coqtop version 8.15.0
   Modules that could not be inlined: Rewriter.Rewriter.Rewriter, Rewriter.Util.TypeList
   Expected coqc runtime on this file: 52.802 sec *)
Require Coq.ZArith.ZArith.
Require Coq.Lists.List.
Require Coq.micromega.Lia.
Require Coq.FSets.FMapPositive.
Require Coq.Classes.Morphisms.
Require Coq.Relations.Relations.
Require Coq.Bool.Bool.
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
Require Rewriter.Util.Tactics.FindHyp.
Require Rewriter.Util.Tactics.UniquePose.
Require Rewriter.Util.Tactics.SpecializeAllWays.
Require Rewriter.Language.Inversion.
Require Rewriter.Util.ListUtil.Forall.
Require Rewriter.Util.Logic.ProdForall.
Require Rewriter.Language.Wf.
Require Coq.MSets.MSetPositive.
Require Rewriter.Util.PrimitiveSigma.
Require Coq.MSets.MSetFacts.
Require Rewriter.Util.Logic.ExistsEqAnd.
Require Rewriter.Util.MSetPositive.Facts.
Require Rewriter.Util.Tactics.PrintContext.
Require Rewriter.Util.Tactics.PrintGoal.
Require Rewriter.Util.Tactics.WarnIfGoalsRemain.
Require Rewriter.Util.Tactics.EvarNormalize.
Require Rewriter.Util.Tactics.ClearFree.
Require Rewriter.Util.Tactics.CacheTerm.
Require Coq.derive.Derive.
Require Rewriter.Language.Pre.
Require Rewriter.Language.IdentifiersBasicLibrary.
Require Rewriter.Language.IdentifiersLibrary.
Require Rewriter.Util.Tactics.DebugPrint.
Require Rewriter.Language.IdentifiersGenerate.
Require Rewriter.Language.IdentifiersLibraryProofs.
Require Rewriter.Language.IdentifiersGenerateProofs.
Require Ltac2.Ltac2.
Require Ltac2.Printf.
Require Ltac2.Ltac1.
Require Rewriter.Util.Tactics2.Ident.
Require Rewriter.Util.Tactics2.Char.
Require Rewriter.Util.TypeList.
Require Rewriter.Language.UnderLets.
Require Rewriter.Rewriter.Rewriter.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export Rewriter_DOT_Util_DOT_Tactics2_DOT_String_WRAPPED.
Module Export String.
Import Ltac2.Ltac2.
Export Rewriter.Util.FixCoqMistakes.

 
Ltac2 null () : string := String.make 1 (Char.null ()).
Ltac2 backspace () : string := String.make 1 (Char.backspace ()).
Ltac2 tab () : string := String.make 1 (Char.tab ()).
Ltac2 lf () : string := String.make 1 (Char.lf ()).
Ltac2 newpage () : string := String.make 1 (Char.newpage ()).
Ltac2 cr () : string := String.make 1 (Char.cr ()).
Ltac2 escape () : string := String.make 1 (Char.escape ()).
Ltac2 newline () : string := String.make 1 (Char.newline ()).

End String.

End Rewriter_DOT_Util_DOT_Tactics2_DOT_String_WRAPPED.
Module Export Rewriter_DOT_Util_DOT_Tactics2_DOT_String.
Module Export Rewriter.
Module Export Util.
Module Export Tactics2.
Module Export String.
Include Rewriter_DOT_Util_DOT_Tactics2_DOT_String_WRAPPED.String.
End String.

End Tactics2.

End Util.

End Rewriter.

End Rewriter_DOT_Util_DOT_Tactics2_DOT_String.
Module Export Message.
Import Ltac2.Ltac2.
Import Ltac2.Printf.

Ltac2 of_list (pr : 'a -> message) (ls : 'a list) : message
  := fprintf
       "[%a]"
       (fun () a => a)
       (match ls with
        | [] => fprintf ""
        | x :: xs
          => List.fold_left (fun init x => fprintf "%a, %a" (fun () a => a) init (fun () => pr) x) xs (pr x)
        end).

Ltac2 of_binder (b : binder) : message
  := fprintf "%a : %t" (fun () a => a) (match Constr.Binder.name b with
                                        | Some n => fprintf "%I" n
                                        | None => fprintf ""
                                        end)
             (Constr.Binder.type b).
Module Export Ltac1.

Ltac2 Type exn ::= [ Not_a_constr (string, Ltac1.t) ].

#[deprecated(since="8.15",note="Use Ltac2 instead.")]
 Ltac2 get_to_constr (debug_name : string) v :=
  match Ltac1.to_constr v with
  | Some v => v
  | None => Control.throw (Not_a_constr debug_name v)
  end.

#[deprecated(since="8.15",note="Use Ltac2 instead.")]
 Ltac2 apply_c (f : Ltac1.t) (args : constr list) : constr :=
  '(ltac2:(Ltac1.apply f (List.map Ltac1.of_constr args) (fun v => Control.refine (fun () => get_to_constr "apply_c:arg" v)))).
Import Ltac2.Constr.Unsafe.

Ltac2 mkApp (f : constr) (args : constr list) :=
  make (App f (Array.of_list args)).
Ltac2 mkLambda b (body : constr) :=
  make (Lambda b body).
Ltac2 mkLetIn (b : binder) (val : constr) (body : constr) :=
  make (LetIn b val body).
Ltac2 mkRel (i : int) :=
  make (Rel i).
Ltac2 mkVar (i : ident) :=
  make (Var i).
Import Rewriter.Language.Language.
Import Rewriter.Util.LetIn.
Import Rewriter.Util.ListUtil.
Import Rewriter.Util.Option.
Import Rewriter.Util.Prod.
Import Rewriter.Util.NatUtil.
Import Rewriter.Util.Bool.
Module Export Compilers.
  Export Language.Compilers.
  Module Export Exports.
    Ltac2 Type exn ::= [ Reification_failure (message) ].
    Ltac2 Type exn ::= [ Reification_panic (message) ].
  End Exports.

  Module Import Ltac2.
    Module Export Ident.

      Ltac constant_to_lambda_reified cst :=
        let cst := fresh "reified_" cst in constr:(fun cst : True => cst).
      Ltac2 refine_constant_to_lambda_reified (c : Ltac1.t) : unit :=
        let f := ltac1:(c |- let v := constant_to_lambda_reified constr:(c) in exact v) in
        f c.
      Ltac2 reified_of_constr (c : constr) : ident
        := Ident.of_constr refine_constant_to_lambda_reified c.
    End Ident.
  End Ltac2.

  Ltac2 with_term_in_context (cache : (unit -> binder) list) (tys : constr list) (term : constr) (tac : constr -> unit) : unit :=
    printf "Warning: with_term_in_context: Bad asymptotics";
    let rec aux0 (cache : (unit -> binder) list) (avoid : Fresh.Free.t) (k : unit -> unit)
      := match cache with
         | [] => k ()
         | b :: bs
           => let b := b () in
              let id := match Constr.Binder.name b with
                        | Some id => id
                        | None => Fresh.fresh avoid @DUMMY_with_term_in_context_MISSING
                        end in
              let avoid := Fresh.Free.union avoid (Fresh.Free.of_ids [id]) in
              let _ := Constr.in_context id (Constr.Binder.type b) (fun () => aux0 bs avoid k; Control.refine (fun () => 'I)) in
              ()
         end in
    let rec aux (tys : constr list) (acc : ident list) (avoid : Fresh.Free.t)
      := match tys with
         | [] => aux0 cache avoid (fun () => tac (Constr.Unsafe.substnl (List.map mkVar (List.rev acc)) 0 term))
         | ty :: tys
           => let id := Fresh.fresh avoid @DUMMY in
              let avoid := Fresh.Free.union avoid (Fresh.Free.of_ids [id]) in
              let _ := Constr.in_context id ty (fun () => aux tys (id :: acc) avoid; Control.refine (fun () => 'I)) in
              ()
         end in
    aux tys [] (Fresh.Free.of_constr term).

  Module Export Reify.
    Ltac2 debug_level := Pre.reify_debug_level.

    Ltac2 mutable should_debug_enter_reify () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_enter_reify_preprocess () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_enter_reify_ident_preprocess () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_enter_reify_after_preprocess () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_leave_reify_success () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_leave_reify_failure () := Int.le 0 debug_level.
    Ltac2 mutable should_debug_leave_reify_normal_failure () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_enter_reify_ident_after_preprocess () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_enter_lookup_ident () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_success () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_failure_verbose () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_failure () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_enter_plug_template_ctx () := Int.le 7 debug_level.
    Ltac2 mutable should_debug_enter_reify_case () := Int.le 7 debug_level.
    Ltac2 mutable should_debug_fine_grained () := Int.le 100 debug_level.
    Ltac2 mutable should_debug_print_args () := Int.le 50 debug_level.
    Ltac2 mutable should_debug_let_bind () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_typing_failure () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_typing_failure_assume_well_typed () := Int.le 2 debug_level.
    Ltac2 mutable should_debug_check_app_early () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_profile () := Int.le 1 debug_level.

    Ltac2 debug_if (cond : unit -> bool) (tac : unit -> 'a) (default : 'a) :=
      if cond ()
      then tac ()
      else default.

    Ltac2 debug_typing_failure (funname : string) (x : constr) (err : exn)
      := debug_if should_debug_typing_failure (fun () => printf "Warning: %s: failure to typecheck %t: %a" funname x (fun () => Message.of_exn) err) ().
    Ltac2 debug_typing_failure_assume_well_typed (funname : string) (v : constr) (term : constr) (ctx_tys : binder list) (ty : constr)
      := debug_if should_debug_typing_failure_assume_well_typed (fun () => printf "Warning: %s: could not well-type %t due to underlying issue typechecking %t without relevant context %a, but assuming that it's well-typed because %t is not a template-parameter type" funname v term (fun () => Message.of_list Message.of_binder) ctx_tys ty) ().
    Ltac2 debug_profile (descr : string) (f : unit -> 'a) : 'a
      := if should_debug_profile ()
         then Control.time (Some descr) f
         else f ().
    Ltac2 debug_fine_grained (funname : string) (msg : unit -> message)
      := debug_if should_debug_fine_grained (fun () => printf "%s: %a" funname (fun () => msg) ()) ().
    Ltac2 debug_enter_reify (funname : string) (e : constr)
      := debug_if should_debug_enter_reify (fun () => printf "%s: Attempting to reify:" funname; printf "%t" e) ().
    Ltac2 debug_enter_reify_case (funname : string) (casename : string) (e : constr)
      := debug_if should_debug_enter_reify_case (fun () => printf "%s: Case: %s" funname casename) ().
    Ltac2 debug_enter_reify_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_preprocess (fun () => printf "%s: Attempting to preprocess:" funname; printf "%t" e) ().

    Ltac2 debug_enter_reify_after_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_after_preprocess (fun () => printf "%s: Attempting to reify (post-preprocessing):" funname; printf "%t" e) ().
    Ltac2 debug_enter_reify_ident_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_ident_preprocess (fun () => printf "%s: Attempting to (ident) preprocess:" funname; printf "%t" e) ().
    Ltac2 debug_enter_reify_ident_after_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_ident_after_preprocess (fun () => printf "%s: Attempting to reify ident (post-preprocessing):" funname; printf "%t" e) ().
    Ltac2 debug_leave_reify_success (funname : string) (e : constr) (ret : constr)
      := debug_if should_debug_leave_reify_success (fun () => printf "%s: Success in reifying: %t as %t" funname e ret) ().
    Ltac2 debug_leave_reify_failure (funname : string) (e : constr)
      := debug_if should_debug_leave_reify_failure (fun () => printf "%s: Failure in reifying:" funname; printf "%t" e) ().
    Ltac2 debug_leave_reify_normal_failure (funname : string) (e : constr)
      := debug_if should_debug_leave_reify_normal_failure (fun () => printf "%s: Failure in reifying:" funname; printf "%t" e) ().
    Ltac2 debug_enter_lookup_ident (funname : string) (e : constr)
      := debug_if should_debug_enter_lookup_ident (fun () => printf "%s: Attempting to lookup ident:" funname; printf "%t" e) ().
    Ltac2 debug_leave_lookup_ident_success (funname : string) (e : constr) (ret : constr)
      := debug_if should_debug_leave_lookup_ident_success (fun () => printf "%s: Success in looking up ident: %t as %t" funname e ret) ().
    Ltac2 debug_leave_lookup_ident_failure (funname : string) (e : constr) (ls : constr)
      := if should_debug_leave_lookup_ident_failure_verbose ()
         then printf "%s: Failure in looking up:" funname; printf "%t (in %t)" e ls
         else if should_debug_leave_lookup_ident_failure ()
              then printf "%s: Failure in looking up:" funname; printf "%t" e
              else ().
    Ltac2 debug_enter_plug_template_ctx (funname : string) (e : constr) (template_ctx : constr list)
      := debug_if
           should_debug_enter_plug_template_ctx
           (fun ()
            => printf
                 "%s: Attempting to plug template ctx into %t %a"
                 funname e (fun () => Message.of_list (fprintf "%t")) template_ctx)
           ().
    Ltac2 debug_let_bind (funname : string) (name : ident) (ty : constr) (val : constr)
      := debug_if
           should_debug_let_bind
           (fun ()
            => printf "%s: let-binding %I : %t := %t" funname name ty val)
           ().
    Ltac2 debug_print_args (funname : string) (pr : 'a -> message) (args : 'a)
      := debug_if should_debug_print_args (fun () => printf "%s: args: %a" funname (fun () => pr) args) ().
    Ltac2 debug_Constr_check (funname : string) (descr : constr -> constr -> exn -> message) (var : constr) (cache : (unit -> binder) list) (var_ty_ctx : constr list) (e : constr)
      := debug_if
           should_debug_check_app_early
           (fun () => match Constr.Unsafe.check e with
                      | Val e => e
                      | Err _
                        => with_term_in_context
                             cache
                             (List.map (fun t => mkApp var [t]) var_ty_ctx) e
                             (fun e' => match Constr.Unsafe.check e' with
                                        | Val _ =>   ()
                                        | Err err
                                          => let descr := descr e e' err in
                                             Control.throw
                                              (Reification_panic
                                                 (fprintf "Anomaly: %s:%s%t failed to check (in context %a as %t):%s%a" funname (String.newline ()) e (fun () => Message.of_list Message.of_constr) var_ty_ctx e' (String.newline ()) (fun () a => a) descr))
                                        end);
                           e
                      end)
           e.
  End Reify.

  Module Export type.
    Import Language.Compilers.type.
    Ltac2 rec reify (base_reify : constr -> constr) (base_type : constr) (ty : constr) :=
      Reify.debug_enter_reify "type.reify" ty;
      let reify_rec (t : constr) := reify base_reify base_type t in
      let res :=
        lazy_match! (eval cbv beta in $ty) with
        | ?a -> ?b
          => let ra := reify_rec a in
             let rb := reify_rec b in
             '(@arrow $base_type $ra $rb)
        | @interp _ _ ?t => t
        | _ => let rt := base_reify ty in
               '(@base $base_type $rt)
        end in
      Reify.debug_leave_reify_success "type.reify" ty res;
      res.
    #[deprecated(since="8.15",note="Use Ltac2 type.reify instead.")]
     Ltac reify base_reify base_type ty :=
      let f := ltac2:(base_reify base_type ty
                      |- Control.refine (fun () => reify (fun v => Ltac1.apply_c base_reify [v]) (Ltac1.get_to_constr "type.reify:base_type" base_type) (Ltac1.get_to_constr "type.reify:ty" ty))) in
      constr:(ltac:(f base_reify base_type ty)).
  End type.
  Module Export base.
    Import Language.Compilers.base.
    Local Notation einterp := type.interp.

    Ltac2 rec reify (base : constr) (reify_base : constr -> constr) (ty : constr) :=
      let reify_rec (ty : constr) := reify base reify_base ty in
      Reify.debug_enter_reify "base.reify" ty;
      let res :=
        lazy_match! (eval cbv beta in $ty) with
        | Datatypes.unit => '(@type.unit $base)
        | Datatypes.prod ?a ?b
          => let ra := reify_rec a in
             let rb := reify_rec b in
             '(@type.prod $base $ra $rb)
        | Datatypes.list ?t
          => let rt := reify_rec t in
             '(@type.list $base $rt)
        | Datatypes.option ?t
          => let rt := reify_rec t in
             '(@type.option $base $rt)
        | @interp  ?base' ?base_interp ?t => t
        | @einterp (@type  ?base') (@interp  ?base' ?base_interp) (@Compilers.type.base (@type  ?base') ?t) => t
        | ?ty => let rt := reify_base ty in
                 '(@type.type_base $base $rt)
        end in
      Reify.debug_leave_reify_success "base.reify" ty res;
      res.
    #[deprecated(since="8.15",note="Use Ltac2 base.reify instead.")]
     Ltac reify base reify_base ty :=
      let f := ltac2:(base reify_base ty
                      |- Control.refine (fun () => reify (Ltac1.get_to_constr "base" base) (fun v => Ltac1.apply_c reify_base [v]) (Ltac1.get_to_constr "ty" ty))) in
      constr:(ltac:(f base reify_base ty)).
  End base.

  Module Export expr.
    Import Language.Compilers.expr.

    Module Export var_context.
      Inductive list {base_type} {var : type base_type -> Type} :=
      | nil
      | cons {T t} (gallina_v : T) (v : var t) (ctx : list).
    End var_context.

    Ltac2 rec is_template_parameter (ctx_tys : binder list) (parameter_type : constr) : bool :=
      let do_red () :=
        let t := Std.eval_hnf parameter_type in
        if Constr.equal t parameter_type
        then false
        else is_template_parameter ctx_tys t in
      match Constr.Unsafe.kind parameter_type with
      | Constr.Unsafe.Sort _ => true
      | Constr.Unsafe.Cast x _ _ => is_template_parameter ctx_tys x
      | Constr.Unsafe.Prod b body => is_template_parameter (b :: ctx_tys) body
      | Constr.Unsafe.App _ _
        => do_red ()
      | Constr.Unsafe.Constant _ _
        => do_red ()
      | Constr.Unsafe.LetIn _ _ _
        => do_red ()
      | Constr.Unsafe.Case _ _ _ _ _
        => do_red ()
      | Constr.Unsafe.Proj _ _
        => do_red ()
      | _ => false
      end.

    Ltac2 rec template_ctx_to_list (template_ctx : constr) : constr list :=
      lazy_match! template_ctx with
      | tt => []
      | (?arg, ?template_ctx')
        => arg :: template_ctx_to_list template_ctx'
      end.

    Ltac2 rec value_ctx_to_list (value_ctx : constr) : (ident * constr   * constr  ) list
      := lazy_match! value_ctx with
         | var_context.nil => []
         | @var_context.cons ?base_type ?var ?t ?rt ?v ?rv ?rest
           => match Constr.Unsafe.kind v with
              | Constr.Unsafe.Var c
                => (c, rt, rv)
              | _ => Control.zero (Invalid_argument (Some (fprintf "value_ctx_to_list: not a Var: %t (of type %t, mapped to %t : %t)" v t rv rt)))
              end
                :: value_ctx_to_list rest
         end.

    Ltac2 eval_cbv_delta_only (i : Std.reference list) (c : constr) :=
      Std.eval_cbv { Std.rBeta := false; Std.rMatch := false;
                     Std.rFix := false; Std.rCofix := false;
                     Std.rZeta := false; Std.rDelta := false;
                     Std.rConst := i }
                   c.

    Ltac2 Type exn ::= [ Template_ctx_mismatch (constr, constr, constr) ].
    Ltac2 plug_template_ctx (ctx_tys : binder list) (f : constr) (template_ctx : constr list) :=
      Reify.debug_enter_plug_template_ctx "expr.plug_template_ctx" f template_ctx;
      let rec mkargs (ctx_tys : binder list) (f_ty : constr) (template_ctx : constr list) :=
        match template_ctx with
        | [] => (1, [], (fun body => body))
        | arg :: template_ctx'
          => match Constr.Unsafe.kind f_ty with
             | Constr.Unsafe.Cast f_ty _ _
               => mkargs ctx_tys f_ty template_ctx
             | Constr.Unsafe.Prod b f_ty
               => if is_template_parameter ctx_tys (Constr.Binder.type b)
                  then let (rel_base, args, close) := mkargs (b :: ctx_tys) f_ty template_ctx' in
                       (rel_base, arg :: args, close)
                  else let (rel_base, args, close) := mkargs (b :: ctx_tys) f_ty template_ctx' in
                       let rel_base := Int.add rel_base 1 in
                       (rel_base, mkRel rel_base :: args,
                         (fun body => mkLambda b (close body)))
             | _ => let f_ty' := Std.eval_hnf f_ty in
                    if Constr.equal f_ty f_ty'
                    then Control.throw (Template_ctx_mismatch f f_ty arg)
                    else mkargs ctx_tys f_ty' template_ctx
             end
        end in

      match template_ctx with
      | [] => f
      | _::_
        => let (_, args, close) := mkargs ctx_tys (Constr.type f) template_ctx in
           close (mkApp f args)
      end.

    Ltac2 rec reify_preprocess (ctx_tys : binder list) (term : constr) : constr :=
      Reify.debug_enter_reify_preprocess "expr.reify_preprocess" term;
      let reify_preprocess := reify_preprocess ctx_tys in
      let thunk
        :=
        let (cst, cTrue) := let term := '(I : True) in
                            match Constr.Unsafe.kind term with
                            | Constr.Unsafe.Cast _ cst cTrue => (cst, cTrue)
                            | _ => Control.throw (Reification_panic (fprintf "Anomaly: reify_preprocess: %t is not a Cast!" term))
                            end in
        fun (v : constr)
        => let v := Constr.Unsafe.make (Constr.Unsafe.Cast v cst cTrue) in

           let v := '(match $v return unit -> True with x => fun _ : unit => x end) in
           match Constr.Unsafe.kind v with
           | Constr.Unsafe.Lambda x v
             => match Constr.Unsafe.kind v with
                | Constr.Unsafe.Cast v _ _ => mkLambda x v
                | _ => Control.throw (Reification_panic (fprintf "Anomaly: reify_preprocess: %t is not a Cast (from under a Lambda)!" v))
                end
           | _ => Control.throw (Reification_panic (fprintf "Anomaly: reify_preprocess: %t is not a Lambda!" v))
           end in
      match Constr.Unsafe.kind term with
      | Constr.Unsafe.Cast x _ _
        => Reify.debug_enter_reify_case "expr.reify_preprocess" "Cast" term;
           reify_preprocess x
      | Constr.Unsafe.LetIn x a b
        => Reify.debug_enter_reify_case "expr.reify_preprocess" "LetIn" term;
           let v_lam () := mkApp (mkLambda x b) [a] in
           let v_inlined () := Constr.Unsafe.substnl [a] 0 b in
           let tx := Constr.Binder.type x in
           if is_template_parameter ctx_tys tx
           then
             reify_preprocess (v_inlined ())
           else
             let v := v_lam () in
             match Constr.Unsafe.check v   with
             | Val v => reify_preprocess v
             | Err err
               => match Constr.Unsafe.check term with
                  | Val _
                    => Reify.debug_typing_failure "expr.reify_preprocess" v err;
                       reify_preprocess (v_inlined ())
                  | Err err'
                    =>
                      Reify.debug_typing_failure_assume_well_typed "expr.reify_preprocess" v term ctx_tys tx;
                      reify_preprocess v
                  end
           end
      | Constr.Unsafe.Case cinfo ret_ty cinv x branches
        => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case" term;
           match Constr.Unsafe.kind ret_ty with
           | Constr.Unsafe.Lambda xb ret_ty
             => let ty := Constr.Unsafe.substnl [x] 0 ret_ty in
                lazy_match! Constr.Binder.type xb with
                | bool
                  => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case:bool" term;
                     reify_preprocess (mkApp '@Thunked.bool_rect [ty; thunk (Array.get branches 0); thunk (Array.get branches 1); x])
                | prod ?a ?b
                  => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case:prod" term;
                     reify_preprocess (mkApp '@prod_rect_nodep [a; b; ty; Array.get branches 0; x])
                | list ?t
                  => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case:list" term;
                     reify_preprocess (mkApp '@Thunked.list_case [t; ty; thunk (Array.get branches 0); Array.get branches 1; x])
                | option ?t
                  => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case:option" term;
                     reify_preprocess (mkApp '@Thunked.option_rect [t; ty; Array.get branches 0; thunk (Array.get branches 1); x])
                | _ => Reify.debug_enter_reify_preprocess "expr.reify_preprocess_extra" term;
                       reify_preprocess_extra ctx_tys term
                end
           | _ => printf "Warning: non-Lambda case return type %t in %t" ret_ty term;
                  Reify.debug_enter_reify_preprocess "expr.reify_preprocess_extra" term;
                  reify_preprocess_extra ctx_tys term
           end
      | _ => Reify.debug_enter_reify_preprocess "expr.reify_preprocess_extra" term;
             reify_preprocess_extra ctx_tys term
      end.

    Ltac2 rec reify_ident_preprocess (ctx_tys : binder list) (term : constr) : constr :=
      Reify.debug_enter_reify_ident_preprocess "expr.reify_ident_preprocess" term;
      let reify_ident_preprocess := reify_ident_preprocess ctx_tys in
      let handle_eliminator (motive : constr) (rect_arrow_nodep : constr option) (rect_nodep : constr option) (rect : constr) (mid_args : constr list) (cases_to_thunk : constr list)
        := let mkApp_thunked_cases f pre_args
             := Control.with_holes
                  (fun () => mkApp f (List.append pre_args (List.append mid_args (List.map (fun arg => open_constr:(fun _ => $arg)) cases_to_thunk))))
                  (fun fv => match Constr.Unsafe.check fv with
                             | Val fv => fv
                             | Err err => Control.throw err
                             end) in
           let opt_recr (thunked : bool) orect args :=
             match orect with
             | Some rect => (reify_ident_preprocess,
                              if thunked
                              then mkApp_thunked_cases rect args
                              else mkApp rect (List.append args (List.append mid_args cases_to_thunk)))
             | None => Control.zero Match_failure
             end in
           let (f, x) := match! (eval cbv beta in $motive) with
                         | fun _ => ?a -> ?b
                           => opt_recr false rect_arrow_nodep [a; b]
                         | fun _ => ?t
                           => opt_recr true rect_nodep [t]
                         | ?t'
                           => if Constr.equal motive t'
                              then (reify_ident_preprocess_extra ctx_tys, term)
                              else opt_recr false (Some rect) [t']
                         end in
           f x in
      lazy_match! term with
      | Datatypes.S => reify_ident_preprocess 'Nat.succ
      | @Datatypes.prod_rect ?a ?b ?t0
        => handle_eliminator t0 None (Some '(@prod_rect_nodep $a $b)) '(@Datatypes.prod_rect $a $b) [] []
      | @Datatypes.bool_rect ?t0 ?ptrue ?pfalse
        => handle_eliminator t0 None (Some '@Thunked.bool_rect) '(@Datatypes.bool_rect) [] [ptrue; pfalse]
      | @Datatypes.nat_rect ?t0 ?p0
        => handle_eliminator t0 (Some '@nat_rect_arrow_nodep) (Some '@Thunked.nat_rect) '(@Datatypes.nat_rect) [] [p0]
      | ident.eagerly (@Datatypes.nat_rect) ?t0 ?p0
        => handle_eliminator t0 (Some '(ident.eagerly (@nat_rect_arrow_nodep))) (Some '(ident.eagerly (@Thunked.nat_rect))) '(ident.eagerly (@Datatypes.nat_rect)) [] [p0]
      | @Datatypes.list_rect ?a ?t0 ?pnil
        => handle_eliminator t0 (Some '(@list_rect_arrow_nodep $a)) (Some '(@Thunked.list_rect $a)) '(@Datatypes.list_rect $a) [] [pnil]
      | ident.eagerly (@Datatypes.list_rect) ?a ?t0 ?pnil
        => handle_eliminator t0 (Some '(ident.eagerly (@list_rect_arrow_nodep) $a)) (Some '(ident.eagerly (@Thunked.list_rect) $a)) '(ident.eagerly (@Datatypes.list_rect) $a) [] [pnil]
      | @ListUtil.list_case ?a ?t0 ?pnil
        => handle_eliminator t0 None (Some '(@Thunked.list_case $a)) '(@ListUtil.list_case $a) [] [pnil]
      | @Datatypes.option_rect ?a ?t0 ?psome ?pnone
        => handle_eliminator t0 None (Some '(@Thunked.option_rect $a)) '(@Datatypes.option_rect $a) [psome] [pnone]
      | ident.eagerly (?f ?x)
        => reify_ident_preprocess '(ident.eagerly $f $x)
      | ?term => reify_ident_preprocess_extra ctx_tys term
      end.

    Ltac2 Type exn ::= [ Reify_ident_cps_failed ].
    Ltac wrap_reify_ident_cps reify_ident_cps idc :=
      reify_ident_cps
        idc
        ltac:(fun idc => refine idc)
               ltac:(fun _ => ltac2:(Control.zero Reify_ident_cps_failed)).
    Ltac2 reify_ident_opt_of_cps (wrapped_reify_ident_cps : Ltac1.t) : binder list -> constr -> constr option
      := fun ctx_tys idc
         => match Control.case (fun () => Ltac1.apply_c wrapped_reify_ident_cps [idc]) with
            | Val v => let (v, _) := v in Some v
            | Err err
              => match err with
                 | Reify_ident_cps_failed => None
                 | _ => Control.zero err
                 end
            end.

    Ltac2 Type exn ::= [ Not_headed_by_a_constant_under_binders (Constr.Unsafe.kind) ].
    Ltac2 rec head_reference_under_binders (term : constr) : (Std.reference * constr) result :=
      let k := Constr.Unsafe.kind term in
      match k with
      | Constr.Unsafe.App f args => head_reference_under_binders f
      | Constr.Unsafe.Cast c _ _ => head_reference_under_binders c
      | Constr.Unsafe.Lambda _ body => head_reference_under_binders body
      | Constr.Unsafe.Constant c inst => Val (Std.ConstRef c, term)
      | Constr.Unsafe.Var id => Val (Std.VarRef id, term)
      | _ => Err (Not_headed_by_a_constant_under_binders k)
      end.

    Module Export Cache.
      Ltac2 Type elem := { name : ident ; rterm : constr }.

      Ltac2 Type t := (Fresh.Free.t * (constr * elem) list) ref.
      Ltac2 init (avoid : constr) : t
        := let avoid := Fresh.Free.union (Fresh.Free.of_constr avoid) (Fresh.Free.of_goal ()) in
           { contents := (avoid, []) }.
      Ltac2 find_opt (term : constr) (cache : t) : elem option
        := let (_, cache) := cache.(contents) in
           List.assoc_opt Constr.equal term cache.
      Ltac2 Type exn ::= [ Cache_contains_element (constr, constr, constr, elem) ].
      Ltac2 add (head_constant : constr) (term : constr) (rterm : constr) (cache : t) : ident
        := let (avoid, known) := cache.(contents) in
           match List.assoc_opt Constr.equal term known with
           | Some e => Control.throw (Cache_contains_element head_constant term rterm e)

           | None
             => let id := Fresh.fresh avoid (Ident.reified_of_constr head_constant) in
                let avoid := Fresh.Free.union avoid (Fresh.Free.of_ids [id]) in
                let e := { name := id ; rterm := rterm } in
                (cache.(contents) := (avoid, (term, e) :: known));
                id
           end.
      Ltac2 elements (cache : t) : (constr * elem) list
        := let (_, cache) := cache.(contents) in
           cache.

      Ltac2 to_thunked_binder_context (cache : t) : (unit -> binder) list
        := List.rev (List.map (fun (_, e) () => Constr.Binder.make (Some (e.(Cache.name))) (Constr.type (e.(Cache.rterm)))) (Cache.elements cache)).
    End Cache.

    Ltac2 rec reify_in_context_opt (base_type : constr) (ident : constr) (reify_base_type : constr -> constr) (reify_ident_opt : binder list -> constr -> constr option) (var : constr) (term : constr) (ctx_tys : binder list) (var_ty_ctx : constr list) (value_ctx : (ident * constr   * constr  ) list) (template_ctx : constr list) (cache : Cache.t) : constr option :=
      let reify_rec_gen term ctx_tys var_ty_ctx template_ctx := reify_in_context_opt base_type ident reify_base_type reify_ident_opt var term ctx_tys var_ty_ctx value_ctx template_ctx cache in
      let reify_rec term := reify_rec_gen term ctx_tys var_ty_ctx template_ctx in
      let reify_rec_not_head term := reify_rec_gen term ctx_tys var_ty_ctx [] in
      let debug_check e
        := Reify.debug_Constr_check
             "expr.reify_in_context" (fun e e' err => Message.of_exn err) var
             (Cache.to_thunked_binder_context cache)
             var_ty_ctx e in
      let reify_ident_opt term
        := Option.map (fun idc => debug_check (mkApp '(@Ident) [base_type; ident; var; open_constr:(_); idc]))
                      (reify_ident_opt ctx_tys term) in
      Reify.debug_enter_reify "expr.reify_in_context" term;
      Reify.debug_print_args
        "expr.reify_in_context"
        (fun ()
         => fprintf
              "{ base_type= %t ; ident = %t ; var = %t ; term = %t ; ctx_tys = %a ; var_ty_ctx = %a ; value_ctx = %a ; template_ctx = %a }"
              base_type ident var term
              (fun () => Message.of_list (fun v => fprintf "%a : %t" (fun () a => a) (match Constr.Binder.name v with Some n => Message.of_ident n | None => Message.of_string "" end) (Constr.Binder.type v))) ctx_tys
              (fun () => Message.of_list Message.of_constr) var_ty_ctx
              (fun () => Message.of_list (fun (id, t, v) => fprintf "(%I, %t, %t)" id t v)) value_ctx
              (fun () => Message.of_list Message.of_constr) template_ctx) ();
      let found :=
        match Constr.Unsafe.kind term with
        | Constr.Unsafe.Rel n
          => Reify.debug_enter_reify_case "expr.reify_in_context" "Rel" term;
             let rt := List.nth var_ty_ctx (Int.sub n 1) in
             Some (debug_check (mkApp ('@Var) [base_type; ident; var; rt; term]))
        | Constr.Unsafe.Var id
          => Reify.debug_enter_reify_case "expr.reify_in_context" "Var" term;
             Reify.debug_fine_grained "expr.reify_in_context" (fun () => fprintf "Searching in %a" (fun () => Message.of_list (fun (id', x, y) => fprintf "(%I, %t, %t)" id' x y)) value_ctx);
             Option.bind
               (List.find_opt (fun (id', _, _) => Ident.equal id' id) value_ctx)
               (fun (_, rt, rv)
                => Some (debug_check (mkApp ('@Var) [base_type; ident; var; rt; rv])))
        | _ => None
        end in
      let res :=
        match found with
        | Some v => Some v
        | None
          => Reify.debug_enter_reify_case "expr.reify_in_context" "preprocess" term;
             let term := reify_preprocess ctx_tys term in
             Reify.debug_enter_reify_after_preprocess "expr.reify_in_context" term;
             let found :=
               match Constr.Unsafe.kind term with
               | Constr.Unsafe.Cast term _ _
                 => Reify.debug_enter_reify_case "expr.reify_in_context" "Cast" term;
                    Some (reify_rec term)
               | Constr.Unsafe.Lambda x f
                 => Some
                      (Reify.debug_enter_reify_case "expr.reify_in_context" "Lambda" term;
                       let t := Constr.Binder.type x in
                       if is_template_parameter ctx_tys t
                       then match template_ctx with
                            | arg :: template_ctx
                              => Reify.debug_enter_reify_case "expr.reify_in_context" "substnl template arg" term;
                                 reify_rec_gen (Constr.Unsafe.substnl [arg] 0 f) ctx_tys var_ty_ctx template_ctx
                            | []
                              => Control.throw (Reification_panic (fprintf "Empty template_ctx when reifying template binder of type %t" t))
                            end
                       else
                         (Reify.debug_enter_reify_case "expr.reify_in_context" "λ body" term;
                          let rt := type.reify reify_base_type base_type t in
                          let rx := Constr.Binder.make (Constr.Binder.name x) (debug_check (mkApp var [rt])) in
                          Option.map
                            (fun rf => debug_check (mkApp ('@Abs) [base_type; ident; var; rt; open_constr:(_); mkLambda rx rf]))
                            (reify_rec_gen f (x :: ctx_tys) (rt :: var_ty_ctx) template_ctx)))
               | Constr.Unsafe.App c args
                 => Reify.debug_enter_reify_case "expr.reify_in_context" "App (check LetIn)" term;
                    if Constr.equal c '@Let_In
                    then if Int.equal (Array.length args) 4
                         then Reify.debug_enter_reify_case "expr.reify_in_context" "LetIn" term;
                              let (ta, tb, a, b) := (Array.get args 0, Array.get args 1, Array.get args 2, Array.get args 3) in
                              Some
                                (Option.bind
                                   (reify_rec a)
                                   (fun ra
                                    => Option.bind
                                         (reify_rec b)
                                         (fun rb
                                          => lazy_match! rb with
                                             | @Abs _ _ _ ?s ?d ?f
                                               => Some (debug_check (mkApp ('@LetIn) [base_type; ident; var; s; d; ra; f]))
                                             | ?rb => Control.throw (Reification_panic (fprintf "Invalid non-Abs function reification of %t to %t" b rb))
                                             end)))
                         else None
                    else None
               | _ => None
               end in
             match found with
             | Some res => res
             | None
               => Reify.debug_enter_reify_case "expr.reify_in_context" "ident_preprocess" term;
                  let term := reify_ident_preprocess ctx_tys term in
                  Reify.debug_enter_reify_ident_after_preprocess "expr.reify_in_context" term;
                  match reify_ident_opt term with
                  | Some res => Some res
                  | None
                    => Reify.debug_enter_reify_case "expr.reify_in_context" "not ident" term;
                       lazy_match! term with
                       | ?f ?x
                         =>
                           Reify.debug_enter_reify_case "expr.reify_in_context" "App" term;
                           let x_is_template_arg
                             := match Control.case (fun () => Constr.type x) with
                                | Val ty
                                  => let (ty, _) := ty in
                                     is_template_parameter ctx_tys ty
                                | Err err
                                  => Reify.debug_typing_failure "expr.reify_in_context" x err;
                                     false
                                end in
                           if x_is_template_arg
                           then
                             Reify.debug_enter_reify_case "expr.reify_in_context" "accumulate template" term;
                             reify_rec_gen f ctx_tys var_ty_ctx (x :: template_ctx)
                           else
                             (Reify.debug_enter_reify_case "expr.reify_in_context" "App (non-template)" term;
                              Option.bind
                                (reify_rec_gen x ctx_tys var_ty_ctx [])
                                (fun rx
                                 => Option.bind
                                      (reify_rec_gen f ctx_tys var_ty_ctx template_ctx)
                                      (fun rf
                                       => Some (debug_check (mkApp '@App [base_type; ident; var; open_constr:(_); open_constr:(_); rf; rx])))))
                       | _
                         => Reify.debug_enter_reify_case "expr.reify_in_context" "pre-plug template_ctx" term;
                            let term := plug_template_ctx ctx_tys term template_ctx in
                            Reify.debug_enter_reify_case "expr.reify_in_context" "reify_ident_opt" term;
                            match reify_ident_opt term with
                            | Some res => Some res
                            | None
                              => match Cache.find_opt term cache with
                                 | Some id => Some (mkVar (id.(Cache.name)))
                                 | None
                                   => match head_reference_under_binders term with
                                      | Val c
                                        => let (c, h) := c in
                                           Reify.debug_enter_reify_case "expr.reify_in_context" "App Constant (unfold)" term;
                                           let term' := eval_cbv_delta_only [c] term in
                                           if Constr.equal term term'
                                           then printf "Unrecognized (non-unfoldable) term: %t" term;
                                                None
                                           else
                                             match reify_rec term' with
                                             | Some rv
                                               => let id := Cache.add h term rv cache in
                                                  Some (mkVar id)
                                             | None
                                               => printf "Failed to reify %t via unfolding to %t" term term';
                                                  None
                                             end
                                      | Err err => printf "Unrecognized (non-constant-headed) term: %t (%a)" term (fun () => Message.of_exn) err;
                                                   None
                                      end
                                 end
                            end
                       end
                  end
             end
        end in
      match res with
      | Some res
        => Reify.debug_leave_reify_success "expr.reify_in_context" term res;
           Some res
      | None
        => Reify.debug_leave_reify_failure "expr.reify_in_context" term;
           None
      end.

    Ltac2 reify_let_bind_cache (rterm : constr) (cache : Cache.t) : constr :=
      Reify.debug_profile
        "reify_let_bind_cache"
        (fun ()
         => let rec aux (elems : (_ * Cache.elem) list)
              := match elems with
                 | [] => rterm
                 | elem :: elems
                   => let (_, elem) := elem in
                      let (name, rv) := (elem.(Cache.name), elem.(Cache.rterm)) in
                      let rty := Constr.type rv in
                      let x := Constr.Binder.make (Some name) rty in
                      Reify.debug_let_bind "reify_let_bind_cache" name rty rv;
                      let rterm := Constr.in_context
                                     name rty (fun () => let v := aux elems in Control.refine (fun () => v)) in
                      let default () :=
                        printf "Warning: reify_let_bind_cache: not a lambda: %t" rterm;
                        rterm in
                      match Constr.Unsafe.kind rterm with
                      | Constr.Unsafe.Lambda x f
                        => mkLetIn x rv f
                      | _ => default ()
                      end
                 end in
            aux (List.rev (Cache.elements cache))).

    Ltac2 reify_in_context (base_type : constr) (ident : constr) (reify_base_type : constr -> constr) (reify_ident_opt : binder list -> constr -> constr option) (var : constr) (term : constr) (ctx_tys : binder list) (var_ty_ctx : constr list) (value_ctx : (ident * constr   * constr  ) list) (template_ctx : constr list) (cache : Cache.t option) : constr :=
      let cache := match cache with
                   | Some cache => cache
                   | None => Cache.init term
                   end in
      match Reify.debug_profile
              "reify_in_context_opt"
              (fun () => reify_in_context_opt base_type ident reify_base_type reify_ident_opt var term ctx_tys var_ty_ctx value_ctx template_ctx cache)
      with
      | Some v => reify_let_bind_cache v cache
      | None => Control.zero (Reification_failure (fprintf "Failed to reify: %t" term))
      end.

    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac reify_in_context base_type ident reify_base_type reify_ident var term value_ctx template_ctx :=
      let f := ltac2:(base_type ident reify_base_type reify_ident var term value_ctx template_ctx
                      |- let template_ctx := Ltac1.get_to_constr "template_ctx" template_ctx in
                         let value_ctx := Ltac1.get_to_constr "value_ctx" value_ctx in
                         Reify.debug_print_args
                           "ltac:expr.reify_in_context"
                           (fun () => fprintf "{ template_ctx = %t ; value_ctx = %t }" template_ctx value_ctx)
                           ();
                         let template_ctx := template_ctx_to_list template_ctx in
                         let value_ctx := value_ctx_to_list value_ctx in
                         let reify_base_type := fun ty => Ltac1.apply_c reify_base_type [ty] in
                         let reify_ident_opt := reify_ident_opt_of_cps reify_ident in
                         Control.refine (fun () => reify_in_context (Ltac1.get_to_constr "base_type" base_type) (Ltac1.get_to_constr "ident" ident) reify_base_type reify_ident_opt (Ltac1.get_to_constr "var" var) (Ltac1.get_to_constr "term" term) [] [] value_ctx template_ctx None)) in
      constr:(ltac:(f base_type ident reify_base_type ltac:(wrap_reify_ident_cps reify_ident) constr:(var) term value_ctx template_ctx)).

Ltac2 Notation "strategy:(" s(strategy) ")" := s.

Ltac head_under_binders_gen redtac expr :=
  let expr := redtac expr in
  match expr with
  | ?f _ => head_under_binders_gen redtac f
  | fun x : ?T => @?f x
    => lazymatch constr:(fun x : T
                         => ltac:(let f' := (eval cbv beta in (f x)) in
                                  let h := head_under_binders_gen redtac f' in
                                  exact h)) with
       | fun _ => ?f => f
       | ?f => f
       end
  | forall x, @?f x
    => head_under_binders_gen redtac f
  | ?expr => expr
  end.

Ltac head_under_binders expr := head_under_binders_gen ltac:(fun e => e) expr.
Module Export IdentifiersBasicGenerate.
Import Coq.Classes.Morphisms.
Import Coq.Lists.List.
Import Ltac2.Bool.
Import Rewriter.Language.Pre.
Import Rewriter.Util.CPSNotations.
Import Rewriter.Util.Pointed.
Import Rewriter.Util.Bool.Reflect.
Import Rewriter.Util.Tactics.DebugPrint.
Import Rewriter.Util.Tactics.ConstrFail.
Import Rewriter.Util.Tactics.Head.
Import Rewriter.Util.Tactics.CacheTerm.

Import EqNotations.
Module Export Compilers.

  Module Export Basic.
    Export IdentifiersBasicLibrary.Compilers.Basic.

    Ltac eliminate_functional_dependencies term :=
      lazymatch term with
      | ?A -> ?term => term
      | fun _ => ?term => term
      | fun name : ?T => ?F
        => let XXX := fresh "XXX" in
           let term := constr:(fun XXX : T
                               => match XXX return _ with name => F end) in
           constr_fail_with ltac:(fun _ => fail 1 "cannot eliminate functional dependencies of" term)
      | forall name : ?T, ?F
        => let XXX := fresh "XXX" in
           let term := constr:(forall XXX : T,
                                  match XXX return _ with name => F end) in
           constr_fail_with ltac:(fun _ => fail 1 "cannot eliminate functional dependencies of" term)
      end.

    Module Export ScrapeTactics.
      Ltac heuristic_process_rules_proofs rules_proofs :=
        let get_prim_fst v :=
            lazymatch v with
            | PrimitiveProd.Primitive.pair ?x ?y => x
            | _ => constr:(PrimitiveProd.Primitive.fst v)
            end in
        let get_prim_snd v :=
            lazymatch v with
            | PrimitiveProd.Primitive.pair ?x ?y => y
            | _ => constr:(PrimitiveProd.Primitive.snd v)
            end in
        let get_fst v :=
            lazymatch v with
            | Datatypes.pair ?x ?y => x
            | _ => constr:(Datatypes.fst v)
            end in
        let get_snd v :=
            lazymatch v with
            | Datatypes.pair ?x ?y => y
            | _ => constr:(Datatypes.snd v)
            end in
        lazymatch type of rules_proofs with
        | PrimitiveHList.hlist (@snd bool Prop) _ => rules_proofs
        | PrimitiveProd.Primitive.prod (@snd bool Prop ?lem) _
          => let fst_part := get_prim_fst rules_proofs in
             let snd_part := get_prim_snd rules_proofs in
             let snd_part := heuristic_process_rules_proofs snd_part in
             let rest := lazymatch type of snd_part with PrimitiveHList.hlist (@snd bool Prop) ?rest => rest end in
             constr:(PrimitiveProd.Primitive.pair fst_part snd_part
                     : PrimitiveHList.hlist (@snd bool Prop) (Datatypes.cons lem rest))
        | PrimitiveProd.Primitive.prod (PrimitiveHList.hlist (@snd bool Prop) Datatypes.nil) _
          => let snd_part := get_prim_snd rules_proofs in
             let snd_part := heuristic_process_rules_proofs snd_part in
             snd_part
        | PrimitiveProd.Primitive.prod (PrimitiveProd.Primitive.prod ?P1 ?P2) ?rest
          => let fst_part := get_prim_fst rules_proofs in
             let snd_part := get_prim_snd rules_proofs in
             let fst_fst_part := get_prim_fst fst_part in
             let snd_fst_part := get_prim_snd fst_part in
             heuristic_process_rules_proofs
               (@PrimitiveProd.Primitive.pair
                  P1 (PrimitiveProd.Primitive.prod P2 rest)
                  fst_fst_part (@PrimitiveProd.Primitive.pair P2 rest snd_fst_part snd_part))
        | PrimitiveProd.Primitive.prod (PrimitiveHList.hlist (@snd bool Prop) (Datatypes.cons ?P ?Ps)) ?rest
          => let fst_part := get_prim_fst rules_proofs in
             let snd_part := get_prim_snd rules_proofs in
             let fst_fst_part := get_prim_fst fst_part in
             let snd_fst_part := get_prim_snd fst_part in
             let P1 := constr:(@snd bool Prop P) in
             let P2 := constr:(PrimitiveHList.hlist (@snd bool Prop) Ps) in
             heuristic_process_rules_proofs
               (@PrimitiveProd.Primitive.pair
                  P1 (PrimitiveProd.Primitive.prod P2 rest)
                  fst_fst_part (@PrimitiveProd.Primitive.pair P2 rest snd_fst_part snd_part))
        | PrimitiveProd.Primitive.prod (Datatypes.prod ?P1 ?P2) ?rest
          => let fst_part := get_prim_fst rules_proofs in
             let snd_part := get_prim_snd rules_proofs in
             let fst_fst_part := get_fst fst_part in
             let snd_fst_part := get_snd fst_part in
             heuristic_process_rules_proofs
               (@PrimitiveProd.Primitive.pair
                  P1 (PrimitiveProd.Primitive.prod P2 rest)
                  fst_fst_part (@PrimitiveProd.Primitive.pair P2 rest snd_fst_part snd_part))
        | PrimitiveProd.Primitive.prod (@RewriteRuleNotations.Types.eval_rect ?TT ?T) ?rest
          => let fst_part := get_prim_fst rules_proofs in
             let snd_part := get_prim_snd rules_proofs in
             let fst_part := heuristic_process_rules_proofs (fst_part : @RewriteRuleNotations.Types.eval_rect TT T) in
             heuristic_process_rules_proofs
               (@PrimitiveProd.Primitive.pair _ rest fst_part snd_part)
        | PrimitiveProd.Primitive.prod ?P ?rest
          => heuristic_process_rules_proofs (rules_proofs : PrimitiveProd.Primitive.prod (@snd bool Prop (RewriteRuleNotations.Types.default_do_again P)) rest)
        | Datatypes.prod ?P ?rest
          => let fst_part := get_fst rules_proofs in
             let snd_part := get_snd rules_proofs in
             heuristic_process_rules_proofs (@PrimitiveProd.Primitive.pair P rest fst_part snd_part)
        | Datatypes.unit
          => constr:(rules_proofs : PrimitiveHList.hlist (@snd bool Prop) Datatypes.nil)
        | @snd bool Prop ?P
          => constr:(PrimitiveProd.Primitive.pair rules_proofs tt
                     : PrimitiveHList.hlist (@snd bool Prop) (Datatypes.cons P Datatypes.nil))
        | RewriteRuleNotations.Types.eval_rect ?T
          => lazymatch (eval hnf in (_ : rules_proofs_for_eager_type T)) with
             | existT _ ?ty ?val
               => heuristic_process_rules_proofs (val : PrimitiveHList.hlist (@snd bool Prop) ty)
             end
        | ?P => constr:(PrimitiveProd.Primitive.pair rules_proofs tt
                        : PrimitiveHList.hlist (@snd bool Prop) (Datatypes.cons (RewriteRuleNotations.Types.default_do_again P) Datatypes.nil))
        end.

      Ltac make_rules_proofsT_with_args :=
        idtac;
        lazymatch goal with
        | [ |- rules_proofsT_with_args ?rules_proofs ]
          => (tryif has_evar rules_proofs
               then fail 0 "Unresolved evar in" rules_proofs "Rewrite rules are not allowed to contain evars"
               else let res := heuristic_process_rules_proofs rules_proofs in
                    let T := type of res in
                    eexists; exact (@id T res))
        end.

      Ltac2 scrape_preprocess (t : constr) : constr :=
        let t := Compilers.expr.reify_preprocess [] t in
        let t := Compilers.expr.reify_ident_preprocess [] t in
        t.
      Ltac scrape_preprocess t :=
        let f := ltac2:(t |- Control.refine (fun () => scrape_preprocess (Option.get (Ltac1.to_constr t)))) in
        constr:(ltac:(f t)).

      Ltac scrape_data_of_type' scrape_data_of_term so_far T :=
        let recr := scrape_data_of_type' scrape_data_of_term in
        let T := scrape_preprocess T in
        let is_var_T := match constr:(Set) with
                        | _ => let __ := match constr:(Set) with _ => is_var T end in
                               true
                        | _ => false
                        end in
        lazymatch is_var_T with
        | true => so_far
        | false
          => lazymatch T with
             | forall x : ?T, @?F x => recr so_far F
             | Type => so_far
             | Set => so_far
             | Prop => so_far
             | Datatypes.list   => so_far
             | Datatypes.option   => so_far
             | Datatypes.unit   => so_far
             | Datatypes.prod   => so_far
             | ?x = ?y
               => let so_far := scrape_data_of_term so_far x in
                  scrape_data_of_term so_far y
             | ?f ?x
               => let so_far := recr so_far f in
                  recr so_far x
             | fun x : ?T => ?F
               => let so_far := recr so_far T in
                  let F' := fresh in
                  eliminate_functional_dependencies
                    (fun x : T =>
                       match F return _ with
                       | F' =>
                         ltac:(
                           let F := (eval cbv delta [F'] in F') in
                           clear F';
                           let so_far := recr so_far F in
                           exact so_far)
                       end)
             | ?ty
               => let base_type_list_named := lazymatch so_far with {| ScrapedData.base_type_list_named := ?base_type_list_named |} => base_type_list_named end in
                  lazymatch base_type_list_named with
                  | context[InductiveHList.cons {| Named.value := ty |}]
                    => so_far
                  | _ => lazymatch so_far with
                         | {| ScrapedData.all_ident_named_interped := ?all_ident_named_interped
                              ; ScrapedData.base_type_list_named := ?base_type_list_named |}
                           => constr:({| ScrapedData.all_ident_named_interped := all_ident_named_interped
                                         ; ScrapedData.base_type_list_named := InductiveHList.cons (without_name ty) base_type_list_named |})
                         end
                  end
             end
        end.

      Ltac require_type_or_arrow T :=
        lazymatch (eval cbv beta in T) with
        | Type => idtac
        | Set => idtac
        | Prop => idtac
        | forall x : ?A, @?F x
          => let __ := constr:(forall x : A,
                                  ltac:(require_type_or_arrow (F x); exact True)) in
             idtac
        end.

      Ltac scrape_data_of_term so_far term :=
        let scrape_data_of_type := scrape_data_of_type' scrape_data_of_term in
        let recr := scrape_data_of_term in
        let term := scrape_preprocess term in
        let is_var_term := match constr:(Set) with
                           | _ => let __ := match constr:(Set) with _ => is_var term end in
                                  true
                           | _ => false
                           end in
        let is_a_type :=
            let T := type of term in
            match constr:(Set) with
            | _ => let __ := match constr:(Set) with _ => require_type_or_arrow T end in
                   true
            | _ => false
            end in
        let try_add term :=
            let all_ident_named_interped := lazymatch so_far with {| ScrapedData.all_ident_named_interped := ?all_ident_named_interped |} => all_ident_named_interped end in
            lazymatch all_ident_named_interped with
            | context[InductiveHList.cons {| Named.value := term |}]
              => so_far
            | _ => lazymatch so_far with
                   | {| ScrapedData.all_ident_named_interped := ?all_ident_named_interped
                        ; ScrapedData.base_type_list_named := ?base_type_list_named |}
                     => constr:({| ScrapedData.all_ident_named_interped := InductiveHList.cons (without_name term) all_ident_named_interped
                                   ; ScrapedData.base_type_list_named := base_type_list_named |})
                   end
            end in
        lazymatch is_var_term with
        | true => so_far
        | false =>
          lazymatch is_a_type with
          | true => scrape_data_of_type so_far term
          | false =>
            lazymatch term with
            | ident.eagerly ?t => try_add term
            | ?f ?x
              => let so_far := recr so_far f in
                 recr so_far x
            | fun x : ?T => ?F
              => let so_far := scrape_data_of_type so_far T in
                 let F' := fresh in
                 eliminate_functional_dependencies
                   (fun x : T =>
                      match F return _ with
                      | F' =>
                        ltac:(
                          let F := (eval cbv delta [F'] in F') in
                          clear F';
                          let so_far := recr so_far F in
                          exact so_far)
                      end)
            | ?term => try_add term
            end
          end
        end.

      Ltac scrape_data_of_type so_far T
        := scrape_data_of_type' scrape_data_of_term so_far T.

      Notation initial_type_list :=
        ([without_name Datatypes.nat
          ; without_name Datatypes.bool]%hlist)
          (only parsing).
      Notation initial_term_list :=
        ([without_name (@ident.literal)
          ; without_name (@Datatypes.nil)
          ; without_name (@Datatypes.cons)
          ; without_name (@Datatypes.Some)
          ; without_name (@Datatypes.None)
          ; without_name (@Datatypes.pair)
          ; without_name (@Datatypes.tt)
          ; without_name (@prod_rect_nodep)
          ; without_name (@Thunked.bool_rect)
          ; without_name (@Thunked.list_case)
          ; without_name (@Thunked.option_rect)
          ; with_name ident_nat_rect (@Thunked.nat_rect)
          ; with_name ident_eager_nat_rect (ident.eagerly (@Thunked.nat_rect))
          ; with_name ident_nat_rect_arrow (@nat_rect_arrow_nodep)
          ; with_name ident_eager_nat_rect_arrow (ident.eagerly (@nat_rect_arrow_nodep))
          ; with_name ident_list_rect (@Thunked.list_rect)
          ; with_name ident_eager_list_rect (ident.eagerly (@Thunked.list_rect))
          ; with_name ident_list_rect_arrow (@list_rect_arrow_nodep)
          ; with_name ident_eager_list_rect_arrow (ident.eagerly (@list_rect_arrow_nodep))
          ; with_name ident_List_nth_default (@nth_default)
          ; with_name ident_eager_List_nth_default (ident.eagerly (@nth_default))
         ]%hlist)
          (only parsing).

      Ltac scrape_data_of_rulesT rules extra :=
        let rec iter so_far ls :=
            lazymatch (eval hnf in ls) with
            | Datatypes.cons (_, ?T) ?rest
              => let so_far := scrape_data_of_type so_far T in
                 iter so_far rest
            | Datatypes.nil => so_far
            | ?term => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-list-of-pair rewrite rules" term)
            end in
        let so_far :=
            iter {| ScrapedData.all_ident_named_interped := initial_term_list
                    ; ScrapedData.base_type_list_named := initial_type_list |}
                 rules in
        let extraT := type of extra in
        let so_far := scrape_data_of_type so_far extraT in
        let so_far := scrape_data_of_term so_far extra in
        so_far.

      Ltac build_scrape_data rules_proofs extra :=
        let expected_type := uconstr:(PrimitiveHList.hlist (@snd bool Prop) ?[rewrite_rules]) in
        lazymatch (type of rules_proofs) with
        | PrimitiveHList.hlist _ ?rewrite_rulesT
          => scrape_data_of_rulesT rewrite_rulesT extra
        | ?T => constr_fail_with ltac:(fun _ => fail 1 "Unexpected type" T "of rewrite rules proofs" rules_proofs "; expected" expected_type)
        end.
      Ltac make_scrape_data_via rules_proofs extra :=
        let res := build_scrape_data rules_proofs extra in refine res.
      Ltac make_scrape_data :=
        idtac;
        lazymatch goal with
        | [ |- ScrapedData.t_with_args ?rules_proofs ?extra ]
          => cbv [ScrapedData.t_with_args];
             make_scrape_data_via rules_proofs extra
        | [ |- ?G ]
          => let exp := uconstr:(ScrapedData.t_with_args ?[rules_proofs] ?[extra]) in
             fail 0 "Unexpected goal:" G "(expected" exp ")"
        end.
    End ScrapeTactics.

    Module Import Tactics.

      Ltac check_debug_level_then_Set _ :=
        let lvl := ident_basic_assembly_debug_level in
        lazymatch type of lvl with
        | nat => constr:(Set)
        | ?T => constr_run_tac ltac:(fun _ => idtac "Error: ident_basic_assembly_debug_level should have type nat but instead has type" T)
        end.
      Ltac debug1 tac :=
        let lvl := ident_basic_assembly_debug_level in
        lazymatch lvl with
        | S _ => constr_run_tac tac
        | _ => check_debug_level_then_Set ()
        end.

      Ltac get_min_and_incr min :=
        lazymatch min with
        | S ?min => let v := get_min_and_incr min in
                    constr:(S v)
        | ?ev => let unif := open_constr:(eq_refl : S _ = ev) in
                 O
        end.
      Ltac build_index_of_base base :=
        constr:(ltac:(let t := fresh "t" in
                      let min := open_constr:(_ : Datatypes.nat) in
                      unshelve (intro t; destruct t;
                                [ > let v := get_min_and_incr min in refine v .. ]);
                      exact O)
                : base -> Datatypes.nat).

      Ltac build_base_eq_dec base :=
        constr:(ltac:(decide equality)
                : forall x y : base, {x = y} + {x <> y}).

      Ltac build_eta_base_cps_gen base :=
        constr:(ltac:((unshelve eexists; let t := fresh in intro t; destruct t); shelve_unifiable; reflexivity)
                : forall (P : base -> Type)
                         (f : forall t, P t),
                   { f' : forall t, P t | forall t, f' t = f t }).

      Ltac build_eta_base_cps eta_base_cps_gen :=
        constr:((fun P f => proj1_sig (@eta_base_cps_gen _ f))
                : forall {P : _ -> Type} (f : forall t, P t) t, P t).

      Ltac build_base_interp eta_base_cps base_type_list index_of_base :=
        let eta_base_cps := (eval cbv in eta_base_cps) in
        let base_type_list := (eval hnf in base_type_list) in
        let index_of_base := (eval cbv in index_of_base) in
        (eval cbv [TypeList.nth] in
            (fun ty => @eta_base_cps (fun _ => Type) (fun t => TypeList.nth (index_of_base t) base_type_list True) ty)).

      Ltac find_evar_tail x :=
        lazymatch x with
        | Datatypes.cons _ ?x => find_evar_tail x
        | ?ev => let __ := match goal with _ => is_evar ev end in
                 ev
        end.
      Ltac build_all_gen T mk P :=
        let res := open_constr:(_ : list T) in
        let fill_next v :=
            let next := find_evar_tail res in
            let __ := open_constr:(eq_refl : next = v) in
            constr:(I) in
        let __ := open_constr:(
                    ltac:(intros;
                          let v' := fresh "v'" in
                          lazymatch goal with
                          | [ v : _ |- _ ] => pose v as v'; destruct v
                          end;
                          let v := (eval cbv [v'] in v') in
                          let h := head v in
                          let v' := mk h in
                          let __ := fill_next open_constr:(Datatypes.cons v' _) in
                          constructor)
                    : P) in
        let __ := fill_next uconstr:(Datatypes.nil) in
        res.
      Ltac build_all_base base :=
        build_all_gen base ltac:(fun x => x) (base -> True).

      Ltac build_all_base_and_interp all_base base_interp :=
        let all_base := (eval cbv in all_base) in
        let base_interp_head := head base_interp in
        (eval cbv [List.map base_interp_head] in
            (List.map (fun v => (v, base_interp v : Type)) all_base)).

      Ltac build_base_type_list base_type_list_named :=
        let rec iter ls :=
            lazymatch (eval hnf in ls) with
            | InductiveHList.nil => TypeList.nil
            | InductiveHList.cons {| Named.value := ?T |} ?rest
              => let rest := iter rest in
                 constr:(TypeList.cons T rest)
            end in
        iter base_type_list_named.

      Ltac2 reify_base_via_list_opt (base : constr) (base_interp : constr) (all_base_and_interp : constr) :=
        let all_base_and_interp := Std.eval_hnf all_base_and_interp in
        let all_base_and_interp := Std.eval_cbv (strategy:(beta)) all_base_and_interp in
        fun ty
        => let ty := Std.eval_cbv (strategy:(beta)) ty in
           Reify.debug_enter_reify "reify_base_via_list" ty;
           let rty := match! all_base_and_interp with
                      | context[Datatypes.cons (?rty, ?ty')]
                        => if Constr.equal ty ty'
                           then Some rty
                           else Control.zero Match_failure
                      | _ => None
                      end in
           match rty with
           | Some rty => Some rty
           | None
             =>
               match! ty with
               | ?base_interp' ?t
                 => if Constr.equal base_interp' base_interp
                    then Some t
                    else Control.zero Match_failure
               | @base.interp ?base' ?base_interp' (@base.type.type_base ?base' ?t)
                 => if Constr.equal base_interp' base_interp && Constr.equal base base
                    then Some t
                    else Control.zero Match_failure
               | @type.interp (base.type ?base') (@base.interp ?base' ?base_interp') (@Compilers.type.base (base.type ?base') (@base.type.type_base ?base' ?t))
                 => if Constr.equal base_interp' base_interp && Constr.equal base base
                    then Some t
                    else Control.zero Match_failure
               | _ => None
               end
           end.
      Ltac2 reify_base_via_list (base : constr) (base_interp : constr) (all_base_and_interp : constr) (ty : constr) : constr :=
        match reify_base_via_list_opt base base_interp all_base_and_interp ty with
        | Some res => res
        | None => Control.zero (Reification_failure (fprintf "Unrecognized type: %t" ty))
        end.

      Ltac2 reify_base_type_via_list (base : constr) (base_interp : constr) (all_base_and_interp : constr) : constr -> constr :=
        Compilers.base.reify base (reify_base_via_list base base_interp all_base_and_interp).

      Ltac build_baseHasNatAndCorrect base_interp :=
        let base_interp_head := head base_interp in
        constr:(ltac:(unshelve eexists; hnf; [ constructor | unshelve econstructor ]; cbv -[base_interp_head]; cbv [base_interp_head];
                      [ match goal with |- nat -> nat => exact (fun x => x) end
                      | match goal with |- nat -> nat => exact (fun x => x) end
                      | exact (fun P x v => v)
                      | exact (fun P x v => v) ])
                : { hasNat : base.type.BaseTypeHasNatT _ & @base.BaseHasNatCorrectT _ base_interp hasNat }).

      Ltac make_baseHasNat baseHasNatAndCorrect :=
        let res := (eval cbv in (projT1 baseHasNatAndCorrect)) in refine res.
      Ltac build_baseHasNat base baseHasNatAndCorrect :=
        constr:(ltac:(make_baseHasNat baseHasNatAndCorrect)
                : base.type.BaseTypeHasNatT base).

      Ltac make_baseHasNatCorrect baseHasNatAndCorrect :=
        let res := (eval cbv in (projT2 baseHasNatAndCorrect)) in refine res.
      Ltac build_baseHasNatCorrect base_interp baseHasNat baseHasNatAndCorrect :=
        constr:(ltac:(make_baseHasNatCorrect baseHasNatAndCorrect)
                : @base.BaseHasNatCorrectT _ base_interp baseHasNat).

      Ltac build_base_beq_and_reflect base :=
        constr:(ltac:(unshelve eexists;
                      [ let x := fresh "x" in
                        let y := fresh "y" in
                        intros x y; destruct x, y
                      | apply reflect_of_beq;
                        [ let x := fresh in
                          let y := fresh in
                          intros x y; destruct x, y; try reflexivity; instantiate (1:=Datatypes.false);
                          intro; exfalso; apply Bool.diff_false_true; assumption
                        | let x := fresh in
                          let y := fresh in
                          intros x y ?; subst y; destruct x; reflexivity ] ])
                : { base_beq : _ & reflect_rel (@eq base) base_beq }).

      Ltac build_base_beq base_beq_and_reflect
        := (eval cbv in (projT1 base_beq_and_reflect)).

      Ltac make_reflect_base_beq base_beq_and_reflect := refine (projT2 base_beq_and_reflect).
      Ltac build_reflect_base_beq base base_beq base_beq_and_reflect :=
        constr:(ltac:(make_reflect_base_beq base_beq_and_reflect)
                : reflect_rel (@eq base) base_beq).

      Ltac build_base_interp_beq base_interp :=
        (eval cbv beta in
            (ltac:(let t1 := fresh "t1" in
                   let t2 := fresh "t2" in
                   intros t1 t2; destruct t1, t2;
                   let h := head base_interp in
                   cbv [h];
                   first [ refine ((fun T (beq : T -> T -> Datatypes.bool) (_ : reflect_rel (@eq T) beq) => beq) _ _ _)
                         | exact (fun _ _ => false) ];
                   lazymatch goal with
                   | [ |- reflect_rel (@eq ?T) _ ]
                     => let exp := uconstr:(reflect_rel (@eq T) ?[beq]) in
                        fail 0 "Could not find a typeclass instance for boolean equality of" T ":" exp
                   end)
             : forall t1 t2, base_interp t1 -> base_interp t2 -> Datatypes.bool)).

      Ltac build_reflect_base_interp_beq base_interp base_interp_beq :=
        constr:(ltac:(let t := fresh "t" in
                      intro t; destruct t; cbv [base_interp base_interp_beq]; typeclasses eauto)
                : forall t, reflect_rel (@eq (base_interp t)) (@base_interp_beq t t)).

      Ltac build_try_make_base_transport_cps base_eq_dec eta_base_cps :=
        constr:((fun (P : _ -> Type) (t1 t2 : _)
                 => @eta_base_cps
                      _
                      (fun t1
                       => @eta_base_cps
                            (fun t2 => ~> option (P t1 -> P t2))
                            (fun t2
                             => match base_eq_dec t1 t2 with
                                | left pf => (return (Some (rew [fun t2 => P t1 -> P t2] pf in id)))
                                | right _ => (return None)
                                end)
                            t2)
                      t1)%cps
                : @type.try_make_transport_cpsT _).

      Ltac build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq :=
        constr:(ltac:(let P := fresh "P" in
                      let t1 := fresh "t1" in
                      let t2 := fresh "t2" in
                      intros P t1 t2; revert P t2; induction t1, t2; cbn;
                      Reflect.reflect_beq_to_eq_using reflect_base_beq; reflexivity)
                : @type.try_make_transport_cps_correctT _ _ try_make_base_transport_cps reflect_base_beq).

      Ltac uneta_fun_push_eagerly term :=
        let term := (eval cbv beta in term) in
        lazymatch term with
        | fun a => ?f a => uneta_fun_push_eagerly f
        | (fun (a : ?A) => @?f a)
          => lazymatch constr:(
                         fun a : A
                         => ltac:(let f' := uneta_fun_push_eagerly (f a) in
                                  exact f')) with
             | fun a => ?f a => uneta_fun_push_eagerly f
             | ?f => f
             end
        | ident.eagerly (?f ?x) => uneta_fun_push_eagerly (ident.eagerly f x)
        | ?f ?x => let f' := uneta_fun_push_eagerly f in
                   let x' := uneta_fun_push_eagerly x in
                   (eval cbv beta in (f' x'))
        | ?f => f
        end.
      Ltac build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident :=
        constr:(ltac:(let ident_interp_head := head ident_interp in
                      let baseHasNat' := (eval hnf in baseHasNat) in
                      let baseHasNatCorrect' := (eval hnf in baseHasNatCorrect) in
                      change baseHasNatCorrect with baseHasNatCorrect';
                      unshelve econstructor; [ econstructor; intros; shelve | constructor ]; intros;
                      lazymatch goal with
                      | [ |- ?ii ?id = ?v ]
                        => let id' := (eval cbv in id) in
                           change (ii id' = v); cbv [ident_interp_head];
                           change baseHasNat with baseHasNat'; cbv [base.of_nat base.to_nat];
                           match goal with
                           | [ |- ?LHS = ?v ] => let v' := uneta_fun_push_eagerly v in change (LHS = v')
                           end;
                           lazymatch goal with
                           | [ |- _ = ?v ]
                             => reify_ident v ltac:(fun idc => let unif := constr:(eq_refl : idc = id') in idtac) ltac:(fun _ => fail 0 "could not reify" v "as an ident")
                           end
                      end; reflexivity)
                : { buildEagerIdent : _ & @ident.BuildInterpEagerIdentCorrectT _ _ _ ident_interp baseHasNat buildEagerIdent baseHasNatCorrect }).

      Ltac make_buildEagerIdent buildEagerIdentAndInterpCorrect :=
        let v := (eval hnf in (projT1 buildEagerIdentAndInterpCorrect)) in
        exact v.
      Ltac build_buildEagerIdent ident baseHasNat buildEagerIdentAndInterpCorrect :=
        constr:(ltac:(make_buildEagerIdent buildEagerIdentAndInterpCorrect)
                : @ident.BuildEagerIdentT _ ident baseHasNat).

      Ltac make_buildInterpEagerIdentCorrect buildEagerIdentAndInterpCorrect :=
        refine (projT2 buildEagerIdentAndInterpCorrect).
      Ltac build_buildInterpEagerIdentCorrect ident_interp buildEagerIdent baseHasNatCorrect buildEagerIdentAndInterpCorrect :=
        constr:(ltac:(make_buildInterpEagerIdentCorrect buildEagerIdentAndInterpCorrect)
                : @ident.BuildInterpEagerIdentCorrectT _ _ _ ident_interp _ buildEagerIdent baseHasNatCorrect).

      Ltac build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent :=
        constr:(ltac:(unshelve eexists; hnf; [ | split ]; cbv;
                      let idc := fresh "idc" in
                      intros ? idc; destruct idc;
                      try (((instantiate (1 := Datatypes.None) + idtac); reflexivity)))
                : { toRestrictedIdent : _
                                        & @ident.ToFromRestrictedIdentT _ _ baseHasNat buildEagerIdent toRestrictedIdent }).

      Ltac make_toRestrictedIdent toRestrictedIdentAndCorrect :=
        let v := (eval hnf in (projT1 toRestrictedIdentAndCorrect)) in
        exact v.
      Ltac build_toRestrictedIdent ident baseHasNat toRestrictedIdentAndCorrect :=
        constr:(ltac:(make_toRestrictedIdent toRestrictedIdentAndCorrect)
                : @ident.ToRestrictedIdentT _ ident baseHasNat).

      Ltac make_toFromRestrictedIdent toRestrictedIdentAndCorrect :=
        let v := (eval hnf in (projT2 toRestrictedIdentAndCorrect)) in
        exact v.
      Ltac build_toFromRestrictedIdent baseHasNat buildEagerIdent toRestrictedIdent toRestrictedIdentAndCorrect :=
        constr:(ltac:(make_toFromRestrictedIdent toRestrictedIdentAndCorrect)
                : @ident.ToFromRestrictedIdentT _ _ baseHasNat buildEagerIdent toRestrictedIdent).

      Ltac build_buildIdentAndInterpCorrect ident_interp reify_ident :=
        constr:(ltac:(let ident_interp_head := head ident_interp in
                      unshelve econstructor;
                      [ econstructor;
                        lazymatch goal with
                        | [ |- ?ident (type.base base.type.unit) ] => solve [ constructor ]
                        | _ => intros; shelve
                        end
                      | constructor ];
                      intros;
                      lazymatch goal with
                      | [ |- ?ii ?id = ?v ]
                        => let id' := (eval cbv in id) in
                           change (ii id' = v); cbv [ident_interp_head];
                           fold (@base.interp);
                           let v := match goal with |- _ = ?v => v end in
                           reify_ident
                             v
                             ltac:(fun idc => let unif := constr:(eq_refl : idc = id') in idtac)
                                    ltac:(fun _ => fail 0 "could not reify" v "as an ident")
                      end; reflexivity)
                : { buildIdent : _
                                 & @ident.BuildInterpIdentCorrectT _ _ _ buildIdent ident_interp }).

      Ltac make_buildIdent buildIdentAndInterpCorrect :=
        let v := (eval hnf in (projT1 buildIdentAndInterpCorrect)) in
        exact v.
      Ltac build_buildIdent base_interp ident buildIdentAndInterpCorrect :=
        constr:(ltac:(make_buildIdent buildIdentAndInterpCorrect)
                : @ident.BuildIdentT _ base_interp ident).

      Ltac make_buildInterpIdentCorrect buildIdentAndInterpCorrect :=
        refine (projT2 buildIdentAndInterpCorrect).
      Ltac build_buildInterpIdentCorrect ident_interp buildIdent buildIdentAndInterpCorrect :=
        constr:(ltac:(make_buildInterpIdentCorrect buildIdentAndInterpCorrect)
                : @ident.BuildInterpIdentCorrectT _ _ _ buildIdent ident_interp).

      Ltac build_ident_is_var_like ident ident_interp var_like_idents :=
        (eval cbv beta zeta in
            (ltac:(let t := fresh "t" in
                   let idc := fresh "idc" in
                   let idc' := fresh "idc'" in
                   let ident_interp_head := head (@ident_interp) in
                   intros t idc; pose (@ident_interp _ idc) as idc';
                   destruct idc; cbn [ident_interp_head] in idc';
                   let idcv := (eval cbv [idc'] in idc') in
                   let idc_head := head idcv in
                   lazymatch (eval hnf in var_like_idents) with
                   | context[InductiveHList.cons idc_head]
                     => refine Datatypes.true
                   | _ => refine Datatypes.false
                   end)
             : forall {t} (idc : ident t), Datatypes.bool)).

      Ltac build_eqv_Reflexive_Proper ident_interp base_interp :=
        constr:(ltac:(let idc := fresh in
                      let ident_interp_head := head ident_interp in
                      let base_interp_head := head base_interp in
                      intros ? idc;
                      destruct idc; cbn [type.eqv ident_interp_head type.interp base.interp base_interp_head];
                      cbv [ident.eagerly];
                      try solve [ typeclasses eauto
                                | cbv [respectful]; repeat intro; subst; cbv; break_innermost_match; eauto using eq_refl with nocore
                                | cbv [respectful]; repeat intro; (apply nat_rect_Proper_nondep || apply list_rect_Proper || apply list_case_Proper || apply list_rect_arrow_Proper); repeat intro; eauto ];
                      match goal with
                      | [ |- ?G ] => idtac "WARNING: Could not automatically prove Proper lemma" G;
                                     idtac "  Please ensure this goal can be solved by typeclasses eauto"
                      end)
                : forall {t} idc, Proper type.eqv (@ident_interp t idc)).

      Ltac make_ident_interp_Proper eqv_Reflexive_Proper :=
        let idc := fresh "idc" in
        let idc' := fresh "idc'" in
        intros ? idc idc' ?; subst idc'; apply eqv_Reflexive_Proper.
      Ltac build_ident_interp_Proper ident_interp eqv_Reflexive_Proper :=
        constr:(ltac:(make_ident_interp_Proper eqv_Reflexive_Proper)
                : forall {t}, Proper (eq ==> type.eqv) (@ident_interp t)).

      Ltac build_invertIdent base_interp ident buildIdent :=
        (eval cbv beta zeta in
            (ltac:(
               let ident_Literal := (eval lazy in (@ident.ident_Literal _ _ _ buildIdent)) in
               let ident_Literal := head_under_binders ident_Literal in
               let ident_nil := (eval lazy in (@ident.ident_nil _ _ _ buildIdent)) in
               let ident_nil := head_under_binders ident_nil in
               let ident_cons := (eval lazy in (@ident.ident_cons _ _ _ buildIdent)) in
               let ident_cons := head_under_binders ident_cons in
               let ident_Some := (eval lazy in (@ident.ident_Some _ _ _ buildIdent)) in
               let ident_Some := head_under_binders ident_Some in
               let ident_None := (eval lazy in (@ident.ident_None _ _ _ buildIdent)) in
               let ident_None := head_under_binders ident_None in
               let ident_pair := (eval lazy in (@ident.ident_pair _ _ _ buildIdent)) in
               let ident_pair := head_under_binders ident_pair in
               let ident_tt := (eval lazy in (@ident.ident_tt _ _ _ buildIdent)) in
               let ident_tt := head_under_binders ident_tt in
               let check_head idc' idc :=
                   let idc' := (eval hnf in idc') in
                   let h := head idc' in
                   constr_eq h idc in
               let bool_by_head idc ridc :=
                   let idc' := fresh "idc'" in
                   pose idc as idc';
                   destruct idc;
                   first [ check_head idc' ridc; exact Datatypes.true
                         | exact Datatypes.false ] in
               let idc := fresh "idc" in
               constructor;
               intros ? idc;
               [ let idc' := fresh "idc'" in
                 pose idc as idc';
                 destruct idc;
                 first [ check_head idc' ident_Literal;
                         refine (Datatypes.Some _);
                         assumption
                       | exact Datatypes.None ]
               | bool_by_head idc ident_nil
               | bool_by_head idc ident_cons
               | bool_by_head idc ident_Some
               | bool_by_head idc ident_None
               | bool_by_head idc ident_pair
               | bool_by_head idc ident_tt ])
             : @invert_expr.InvertIdentT _ base_interp ident)).

      Ltac make_buildInvertIdentCorrect invertIdent buildIdent reflect_base_beq :=
        apply (@HelperLemmas.build_BuildInvertIdentCorrectT_opt _ _ _ invertIdent buildIdent _ reflect_base_beq);
        [ reflexivity.. | ];
        let idc := fresh "idc" in
        intros ? idc; destruct idc; vm_compute; constructor.
      Ltac build_buildInvertIdentCorrect invertIdent buildIdent reflect_base_beq :=
        constr:(ltac:(make_buildInvertIdentCorrect invertIdent buildIdent reflect_base_beq)
                : @invert_expr.BuildInvertIdentCorrectT _ _ _ invertIdent buildIdent).

      Ltac inhabit := (constructor; fail) + (constructor; inhabit).
      Ltac inhabit_or_pointed :=
        once (once (hnf; inhabit)
              + lazymatch goal with
                | [ |- ?G ]
                  => let T := constr:(pointed G) in
                     change T;
                     (exact _ || fail 0 "Could not inhabit" G "; consider adding an instance of type" T)
                end).

      Ltac build_base_default base_interp :=
        let base_interp_head := head base_interp in
        constr:(ltac:(let t := fresh "t" in
                      intro t; destruct t; cbv [base_interp_head]; [ inhabit_or_pointed .. ])
                : @DefaultValue.type.base.DefaultT _ base_interp).

      Ltac build_index_of_ident ident :=
        constr:(ltac:(let t := fresh "t" in
                      let idc := fresh "idc" in
                      let min := open_constr:(_ : Datatypes.nat) in
                      unshelve (intros t idc; destruct idc;
                                [ > let v := get_min_and_incr min in refine v .. ]);
                      exact O)
                : forall t, ident t -> Datatypes.nat).

      Ltac build_ident_interp base_interp ident index_of_ident all_ident_named_interped :=
        let T := constr:(forall t, ident t -> type.interp (base.interp base_interp) t) in
        let res
            := (eval cbv beta iota in
                   (ltac:(let t := fresh "t" in
                          let idc := fresh "idc" in
                          let v := fresh "v" in
                          let index_of_ident := (eval cbv in index_of_ident) in
                          let base_interp_head := head base_interp in
                          let all_ident_named_interped := (eval hnf in all_ident_named_interped) in
                          intros t idc;
                          pose (fun default : False => InductiveHList.nth (@index_of_ident _ idc) all_ident_named_interped default) as v;
                          destruct idc;
                          cbv [InductiveHList.nth InductiveHList.nth_type] in v;
                          let res := lazymatch (eval cbv [v] in v) with
                                     | fun _ => {| Named.value := ?v |} => v
                                     | ?v => constr_fail_with ltac:(fun _ => fail 1 "Invalid interpreted identifier" v)
                                     end in
                          clear v;
                          cbn [type.interp base.interp base_interp_head];
                          apply res; assumption)
                    : T)) in
        constr:(res : T).

      Ltac build_all_idents ident :=
        build_all_gen
          { T : Type & T }
          ltac:(fun h => constr:(existT (fun T => T) _ h))
                 (forall t, ident t -> True).

      Ltac build_all_ident_and_interp all_idents all_ident_named_interped :=
        let all_idents := (eval hnf in all_idents) in
        let all_ident_named_interped := (eval hnf in all_ident_named_interped) in
        lazymatch all_idents with
        | Datatypes.nil
          => lazymatch all_ident_named_interped with
             | InductiveHList.nil => GallinaAndReifiedIdentList.nil
             | _ => constr_fail_with ltac:(fun _ => fail 1 "Invalid remaining interped identifiers" all_ident_named_interped)
             end
        | Datatypes.cons (existT _ _ ?ridc) ?rest_ridc
          => lazymatch all_ident_named_interped with
             | InductiveHList.nil => constr_fail_with ltac:(fun _ => fail 1 "Invalid remaining identifiers" all_idents)
             | InductiveHList.cons {| Named.value := ?vidc |} ?rest_vidc
               => let rest := build_all_ident_and_interp rest_ridc rest_vidc in
                  constr:(GallinaAndReifiedIdentList.cons ridc vidc rest)
             | _ => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-InductiveHList" all_ident_named_interped)
             end
        | _ => constr_fail_with ltac:(fun _ => fail 1 "Invalid non list of existT identifiers" all_idents)
        end.

      Ltac2 rec is_recursively_constructor_or_literal (term : constr) : bool :=
        match Constr.Unsafe.kind term with
        | Constr.Unsafe.Cast term _ _ => is_recursively_constructor_or_literal term
        | Constr.Unsafe.App f args
          => if Constr.equal f '@ident.literal
             then true
             else
               is_recursively_constructor_or_literal f
               && Array.for_all is_recursively_constructor_or_literal args
        | _ => Constr.is_constructor term
        end.

      Ltac2 try_reify_literal (try_reify_base : constr -> constr option) (ident_Literal : constr) (term : constr) : constr option :=
        if is_recursively_constructor_or_literal term
        then
          Option.bind
            (try_reify_base (Constr.type term))
            (fun rt => Some (mkApp ident_Literal [rt; term]))
        else None.

      Ltac2 rec get_head_with_eagerly_then_plug_reified_types (reify_base_type : constr -> constr) (lookup : constr -> constr option) (term : constr) : constr option :=
        let recr := get_head_with_eagerly_then_plug_reified_types reify_base_type lookup in
        lazy_match! term with
        | ident.eagerly ?f => lookup term
        | ?f ?x
          => Option.bind
               (recr f)
               (fun rf
                => lazy_match! Constr.type rf with
                   | forall t, _
                     => let rx := reify_base_type x in
                        Some (mkApp rf [rx])
                   | _ => None
                   end)
        | _ => lookup term
        end.
      Ltac2 reify_ident_from_interp (ident_interp : constr) (term : constr) : constr option :=

        lazy_match! term with
        | ?ident_interp' _ ?idc
          => if Constr.equal ident_interp ident_interp'
             then Some idc
             else None
        | _ => None
        end.

      Ltac2 reify_ident_via_list_opt (base : constr) (base_interp : constr) (all_base_and_interp : constr) (all_ident_and_interp : constr) (ident_interp : constr) : binder list -> constr -> constr option :=
        let all_ident_and_interp := Std.eval_hnf all_ident_and_interp in
        let try_reify_base := reify_base_via_list_opt base base_interp all_base_and_interp in
        let reify_base := reify_base_via_list base base_interp all_base_and_interp in
        let reify_base_type := reify_base_type_via_list base base_interp all_base_and_interp in
        let ident_Literal := let idc := '(@ident.literal) in
                             let found := match! all_ident_and_interp with
                                          | context[GallinaAndReifiedIdentList.cons ?ridc ?idc']
                                            => if Constr.equal idc idc'
                                               then Some ridc
                                               else Control.zero Match_failure
                                          | _ => None
                                          end in
                             match found with
                             | Some ridc => ridc
                             | None => Control.throw (Reification_panic (fprintf "Missing reification for %t in %t" idc all_ident_and_interp))
                             end in
        fun ctx_tys term
        => Reify.debug_enter_reify "reify_ident_via_list_opt" term;
           Reify.debug_enter_reify_case "reify_ident_via_list_opt" "literal?" term;
           let as_lit := try_reify_literal try_reify_base ident_Literal term in
           let res :=
             match as_lit with
             | Some ridc
               => Reify.debug_enter_reify_case "reify_ident_via_list_opt" "literal✓" term;
                  Some ridc
             | None
               => Reify.debug_enter_reify_case "reify_ident_via_list_opt" "interp?" term;
                  let as_interped := reify_ident_from_interp ident_interp term in
                  match as_interped with
                  | Some idc
                    => Reify.debug_enter_reify_case "reify_ident_via_list_opt" "interp✓" term;
                       Some idc
                  | None
                    => Reify.debug_enter_reify_case "reify_ident_via_list_opt" "head eagerly?" term;
                       get_head_with_eagerly_then_plug_reified_types
                         reify_base_type
                         (fun idc
                          => Reify.debug_enter_lookup_ident "reify_ident_via_list_opt" idc;
                             let found := match! all_ident_and_interp with
                                          | context[GallinaAndReifiedIdentList.cons ?ridc ?idc']
                                            => if Constr.equal idc idc'
                                               then Some ridc
                                               else Control.zero Match_failure
                                          | _ => None
                                          end in
                             match found with
                             | Some ridc
                               => Reify.debug_leave_lookup_ident_success "reify_ident_via_list_opt" idc ridc;
                                  Some ridc
                             | None
                               => Reify.debug_leave_lookup_ident_failure "reify_ident_via_list_opt" idc all_ident_and_interp;
                                  None
                             end)
                         term
                  end
             end in
           match res with
           | Some res
             => Reify.debug_leave_reify_success "reify_ident_via_list_opt" term res;
                Some res
           | None
             => Reify.debug_leave_reify_normal_failure "reify_ident_via_list_opt" term;
                None
           end.

      #[deprecated(since="8.15",note="Use Ltac2 reify_ident_via_list_opt instead.")]
       Ltac reify_ident_via_list base base_interp all_base_and_interp all_ident_and_interp ident_interp term then_tac else_tac :=
        let f := ltac2:(base base_interp all_base_and_interp all_ident_and_interp ident_interp term
                        |- match reify_ident_via_list_opt (Ltac1.get_to_constr "base" base) (Ltac1.get_to_constr "base_interp" base_interp) (Ltac1.get_to_constr "all_base_and_interp" all_base_and_interp) (Ltac1.get_to_constr "all_ident_and_interp" all_ident_and_interp) (Ltac1.get_to_constr "ident_interp" ident_interp) [] (Ltac1.get_to_constr "term" term) with
                           | Some v => Control.refine (fun () => '(@Datatypes.Some _ $v))
                           | None => Control.refine (fun () => '(@Datatypes.None unit))
                           end) in
        match constr:(ltac:(f base base_interp all_base_and_interp all_ident_and_interp ident_interp term)) with
        | Datatypes.Some ?v => then_tac v
        | Datatypes.None => else_tac ()
        end.

      Ltac2 reify_package_of_package (pkg : constr) : constr :=
        '(GoalType.exprReifyInfo $pkg).
      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
      Ltac reify_package_of_package pkg :=
        let f := ltac2:(pkg |- let v := reify_package_of_package (Ltac1.get_to_constr "pkg" pkg) in Control.refine (fun () => v)) in
        constr:(ltac:(f pkg)).

      Ltac2 call_with_base_via_reify_package (tac : constr -> constr -> constr -> 'a) (reify_pkg : constr) : 'a :=
        let pkgT := Constr.type reify_pkg in
        let exprInfo := lazy_match! Std.eval_hnf pkgT with @GoalType.ExprReifyInfoT ?exprInfo => Std.eval_hnf exprInfo end in
        let exprReifyInfo := Std.eval_hnf reify_pkg in
        lazy_match! exprInfo with
        | {| Classes.base := ?base
             ; Classes.base_interp := ?base_interp |}
          => lazy_match! exprReifyInfo with
             | {| GoalType.all_base_and_interp := ?all_base_and_interp
                  ; GoalType.all_ident_and_interp := ?all_ident_and_interp |}
               => tac base base_interp all_base_and_interp
             end
        end.

      Ltac2 reify_base_via_reify_package (reify_pkg : constr) : constr -> constr := call_with_base_via_reify_package reify_base_via_list reify_pkg.
      Ltac2 reify_ident_via_reify_package_opt (reify_pkg : constr) : binder list -> constr -> constr option :=
        let pkgT := Constr.type reify_pkg in
        let exprInfo := lazy_match! Std.eval_hnf pkgT with @GoalType.ExprReifyInfoT ?exprInfo => Std.eval_hnf exprInfo end in
        let exprReifyInfo := Std.eval_hnf reify_pkg in
        lazy_match! exprInfo with
        | {| Classes.base := ?base
             ; Classes.base_interp := ?base_interp
             ; Classes.ident_interp := ?ident_interp |}
          => lazy_match! exprReifyInfo with
             | {| GoalType.all_base_and_interp := ?all_base_and_interp
                  ; GoalType.all_ident_and_interp := ?all_ident_and_interp |}
               => reify_ident_via_list_opt base base_interp all_base_and_interp all_ident_and_interp ident_interp
             end
        end.
      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
       Ltac reify_base_via_reify_package reify_pkg ty :=
        let f := ltac2:(reify_pkg ty
                        |- Control.refine (fun () => reify_base_via_reify_package (Ltac1.get_to_constr "reify_pkg" reify_pkg) (Ltac1.get_to_constr "ty" ty))) in
        constr:(ltac:(f reify_pkg ty)).
      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
       Ltac reify_ident_via_reify_package reify_pkg idc :=
        let f := ltac2:(reify_pkg idc
                        |- match reify_ident_via_reify_package_opt (Ltac1.get_to_constr "reify_pkg" reify_pkg) [] (Ltac1.get_to_constr "idc" idc) with
                           | Some v => Control.refine (fun () => '(@Datatypes.Some _ $v))
                           | None => Control.refine (fun () => '(@Datatypes.None unit))
                           end) in
        fun then_tac else_tac
        => match constr:(ltac:(f reify_pkg idc)) with
           | Datatypes.Some ?v => then_tac v
           | Datatypes.None => else_tac ()
           end.

      Ltac cache_build_index_of_base base :=
        let name := fresh "index_of_base" in
        let term := build_index_of_base base in
        cache_term term name.

      Ltac cache_build_base_eq_dec base :=
        let name := fresh "base_eq_dec" in
        let term := build_base_eq_dec base in
        cache_term term name.

      Ltac cache_build_eta_base_cps_gen base :=
        let name := fresh "eta_base_cps_gen" in
        let term := build_eta_base_cps_gen base in
        cache_term term name.

      Ltac cache_build_eta_base_cps eta_base_cps_gen :=
        let name := fresh "eta_base_cps" in
        let term := build_eta_base_cps eta_base_cps_gen in
        cache_term term name.

      Ltac cache_build_base_interp eta_base_cps base_type_list index_of_base :=
        let name := fresh "base_interp" in
        let term := build_base_interp eta_base_cps base_type_list index_of_base in
        let base_interp := cache_term term name in
        let base_interp_head := head base_interp in
        let __ := match goal with _ => set_strategy_expand base_interp_head end in
        base_interp.

      Ltac cache_build_all_base base :=
        let name := fresh "all_base" in
        let term := build_all_base base in
        cache_term term name.

      Ltac cache_build_all_base_and_interp all_base base_interp :=
        let name := fresh "all_base_and_interp" in
        let term := build_all_base_and_interp all_base base_interp in
        cache_term term name.

      Ltac cache_build_base_type_list base_type_list_named :=
        let name := fresh "base_type_list" in
        let term := build_base_type_list base_type_list_named in
        cache_term term name.

      Ltac cache_build_baseHasNatAndCorrect base_interp :=
        let name := fresh "baseHasNatAndCorrect" in
        let term := build_baseHasNatAndCorrect base_interp in
        cache_term term name.

      Ltac cache_build_baseHasNat base baseHasNatAndCorrect :=
        let name := fresh "baseHasNat" in
        let term := build_baseHasNat base baseHasNatAndCorrect in
        cache_term term name.

      Ltac cache_build_baseHasNatCorrect base_interp baseHasNat baseHasNatAndCorrect :=
        let name := fresh "baseHasNatCorrect" in
        let term := build_baseHasNatCorrect base_interp baseHasNat baseHasNatAndCorrect in
        cache_term term name.

      Ltac cache_build_base_beq_and_reflect base :=
        let name := fresh "base_beq_and_reflect" in
        let term := build_base_beq_and_reflect base in
        cache_term term name.

      Ltac cache_build_base_beq base_beq_and_reflect :=
        let name := fresh "base_beq" in
        let term := build_base_beq base_beq_and_reflect in
        cache_term term name.

      Ltac cache_build_reflect_base_beq base base_beq base_beq_and_reflect :=
        let name := fresh "reflect_base_beq" in
        let term := build_reflect_base_beq base base_beq base_beq_and_reflect in
        cache_term term name.

      Ltac cache_build_base_interp_beq base_interp :=
        let name := fresh "base_interp_beq" in
        let term := build_base_interp_beq base_interp in
        cache_term term name.

      Ltac cache_build_reflect_base_interp_beq base_interp base_interp_beq :=
        let name := fresh "reflect_base_interp_beq" in
        let term := build_reflect_base_interp_beq base_interp base_interp_beq in
        cache_term term name.

      Ltac cache_build_try_make_base_transport_cps base_eq_dec eta_base_cps :=
        let name := fresh "try_make_base_transport_cps" in
        let term := build_try_make_base_transport_cps base_eq_dec eta_base_cps in
        cache_term term name.

      Ltac cache_build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq :=
        let name := fresh "try_make_base_transport_cps_correct" in
        let term := build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq in
        cache_term term name.

      Ltac cache_build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident :=
        let name := fresh "buildEagerIdentAndInterpCorrect" in
        let term := build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident in
        cache_term term name.

      Ltac cache_build_buildEagerIdent ident baseHasNat buildEagerIdentAndInterpCorrect :=
        let name := fresh "buildEagerIdent" in
        let term := build_buildEagerIdent ident baseHasNat buildEagerIdentAndInterpCorrect in
        cache_term term name.

      Ltac cache_build_buildInterpEagerIdentCorrect ident_interp buildEagerIdent baseHasNatCorrect buildEagerIdentAndInterpCorrect :=
        let name := fresh "buildInterpEagerIdentCorrect" in
        let term := build_buildInterpEagerIdentCorrect ident_interp buildEagerIdent baseHasNatCorrect buildEagerIdentAndInterpCorrect in
        cache_term term name.

      Ltac cache_build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent :=
        let name := fresh "toRestrictedIdentAndCorrect" in
        let term := build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent in
        cache_term term name.

      Ltac cache_build_toRestrictedIdent ident baseHasNat toRestrictedIdentAndCorrect :=
        let name := fresh "toRestrictedIdent" in
        let term := build_toRestrictedIdent ident baseHasNat toRestrictedIdentAndCorrect in
        cache_term term name.

      Ltac cache_build_toFromRestrictedIdent baseHasNat buildEagerIdent toRestrictedIdent toRestrictedIdentAndCorrect :=
        let name := fresh "toFromRestrictedIdent" in
        let term := build_toFromRestrictedIdent baseHasNat buildEagerIdent toRestrictedIdent toRestrictedIdentAndCorrect in
        cache_term term name.

      Ltac cache_build_buildIdentAndInterpCorrect ident_interp reify_ident :=
        let name := fresh "buildIdentAndInterpCorrect" in
        let term := build_buildIdentAndInterpCorrect ident_interp reify_ident in
        cache_term term name.

      Ltac cache_build_buildIdent base_interp ident buildIdentAndInterpCorrect :=
        let name := fresh "buildIdent" in
        let term := build_buildIdent base_interp ident buildIdentAndInterpCorrect in
        cache_term term name.

      Ltac cache_build_buildInterpIdentCorrect ident_interp buildIdent buildIdentAndInterpCorrect :=
        let name := fresh "buildInterpIdentCorrect" in
        let term := build_buildInterpIdentCorrect ident_interp buildIdent buildIdentAndInterpCorrect in
        cache_term term name.

      Ltac cache_build_ident_is_var_like ident ident_interp var_like_idents :=
        let name := fresh "ident_is_var_like" in
        let term := build_ident_is_var_like ident ident_interp var_like_idents in
        cache_term term name.

      Ltac cache_build_eqv_Reflexive_Proper ident_interp base_interp :=
        let name := fresh "eqv_Reflexive_Proper" in
        let term := build_eqv_Reflexive_Proper ident_interp base_interp in
        cache_term term name.

      Ltac cache_build_ident_interp_Proper ident_interp eqv_Reflexive_Proper :=
        let name := fresh "ident_interp_Proper" in
        let term := build_ident_interp_Proper ident_interp eqv_Reflexive_Proper in
        cache_term term name.

      Ltac cache_build_invertIdent base_interp ident buildIdent :=
        let name := fresh "invertIdent" in
        let term := build_invertIdent base_interp ident buildIdent in
        cache_term term name.

      Ltac cache_build_buildInvertIdentCorrect invertIdent buildIdent reflect_base_beq :=
        let name := fresh "buildInvertIdentCorrect" in
        let term := build_buildInvertIdentCorrect invertIdent buildIdent reflect_base_beq in
        cache_term term name.

      Ltac cache_build_base_default base_interp :=
        let name := fresh "base_default" in
        let term := build_base_default base_interp in
        cache_term term name.

      Ltac cache_build_index_of_ident ident :=
        let name := fresh "index_of_ident" in
        let term := build_index_of_ident ident in
        cache_term term name.

      Ltac cache_build_ident_interp base_interp ident index_of_ident all_ident_named_interped :=
        let name := fresh "ident_interp" in
        let term := build_ident_interp base_interp ident index_of_ident all_ident_named_interped in
        let ident_interp := cache_term term name in
        let ident_interp_head := head ident_interp in
        let __ := match goal with _ => set_strategy_expand ident_interp_head end in
        ident_interp.

      Ltac cache_build_all_idents ident :=
        let name := fresh "all_idents" in
        let term := build_all_idents ident in
        cache_term term name.

      Ltac cache_build_all_ident_and_interp all_idents all_ident_named_interped :=
        let name := fresh "all_ident_and_interp" in
        let term := build_all_ident_and_interp all_idents all_ident_named_interped in
        cache_term term name.
    End Tactics.

    Module Export Tactic.

      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
       Ltac reify_package_of_package := Tactics.reify_package_of_package.
      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
      Ltac reify_base_via_reify_package := Tactics.reify_base_via_reify_package.
      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
      Ltac reify_ident_via_reify_package := Tactics.reify_ident_via_reify_package.

      Ltac build_package base ident base_type_list_named var_like_idents all_ident_named_interped :=
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building index_of_base...") in
        let index_of_base := cache_build_index_of_base base in
        let base_type := constr:(@base.type base) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_type_list...") in
        let base_type_list := cache_build_base_type_list base_type_list_named in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_base_cps_gen...") in
        let eta_base_cps_gen := cache_build_eta_base_cps_gen base in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_base_cps...") in
        let eta_base_cps := cache_build_eta_base_cps eta_base_cps_gen in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_interp...") in
        let base_interp := cache_build_base_interp eta_base_cps base_type_list index_of_base in
        let base_type_interp := constr:(base.interp base_interp) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_base...") in
        let all_base := cache_build_all_base base in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_base_and_interp...") in
        let all_base_and_interp := cache_build_all_base_and_interp all_base base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building index_of_ident...") in
        let index_of_ident := cache_build_index_of_ident ident in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building ident_interp...") in
        let ident_interp := cache_build_ident_interp base_interp ident index_of_ident all_ident_named_interped in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_eq_dec...") in
        let base_eq_dec := cache_build_base_eq_dec base in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_beq_and_reflect...") in
        let base_beq_and_reflect := cache_build_base_beq_and_reflect base in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_beq...") in
        let base_beq := cache_build_base_beq base_beq_and_reflect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building reflect_base_beq...") in
        let reflect_base_beq := cache_build_reflect_base_beq base base_beq base_beq_and_reflect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building baseHasNatAndCorrect...") in
        let baseHasNatAndCorrect := cache_build_baseHasNatAndCorrect base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building baseHasNat...") in
        let baseHasNat := cache_build_baseHasNat base baseHasNatAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building baseHasNatCorrect...") in
        let baseHasNatCorrect := cache_build_baseHasNatCorrect base_interp baseHasNat baseHasNatAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_interp_beq...") in
        let base_interp_beq := cache_build_base_interp_beq base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building reflect_base_interp_beq...") in
        let reflect_base_interp_beq := cache_build_reflect_base_interp_beq base_interp base_interp_beq in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building try_make_base_transport_cps...") in
        let try_make_base_transport_cps := cache_build_try_make_base_transport_cps base_eq_dec eta_base_cps in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building try_make_base_transport_cps_correct...") in
        let try_make_base_transport_cps_correct := cache_build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_idents...") in
        let all_idents := cache_build_all_idents ident in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_ident_and_interp...") in
        let all_ident_and_interp := cache_build_all_ident_and_interp all_idents all_ident_named_interped in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildEagerIdentAndInterpCorrect...") in
        let reify_ident := reify_ident_via_list base base_interp all_base_and_interp all_ident_and_interp (@ident_interp) in
        let buildEagerIdentAndInterpCorrect := cache_build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildEagerIdent...") in
        let buildEagerIdent := cache_build_buildEagerIdent ident baseHasNat buildEagerIdentAndInterpCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildInterpEagerIdentCorrect...") in
        let buildInterpEagerIdentCorrect := cache_build_buildInterpEagerIdentCorrect ident_interp buildEagerIdent baseHasNatCorrect buildEagerIdentAndInterpCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building toRestrictedIdentAndCorrect...") in
        let toRestrictedIdentAndCorrect := cache_build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building toRestrictedIdent...") in
        let toRestrictedIdent := cache_build_toRestrictedIdent ident baseHasNat toRestrictedIdentAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building toFromRestrictedIdent...") in
        let toFromRestrictedIdent := cache_build_toFromRestrictedIdent baseHasNat buildEagerIdent toRestrictedIdent toRestrictedIdentAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildIdentAndInterpCorrect...") in
        let buildIdentAndInterpCorrect := cache_build_buildIdentAndInterpCorrect ident_interp reify_ident in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildIdent...") in
        let buildIdent := cache_build_buildIdent base_interp ident buildIdentAndInterpCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildInterpIdentCorrect...") in
        let buildInterpIdentCorrect := cache_build_buildInterpIdentCorrect ident_interp buildIdent buildIdentAndInterpCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building ident_is_var_like...") in
        let ident_is_var_like := cache_build_ident_is_var_like ident ident_interp var_like_idents in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eqv_Reflexive_Proper...") in
        let eqv_Reflexive_Proper := cache_build_eqv_Reflexive_Proper ident_interp base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building ident_interp_Proper...") in
        let ident_interp_Proper := cache_build_ident_interp_Proper ident_interp eqv_Reflexive_Proper in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building invertIdent...") in
        let invertIdent := cache_build_invertIdent base_interp ident buildIdent in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildInvertIdentCorrect...") in
        let buildInvertIdentCorrect := cache_build_buildInvertIdentCorrect invertIdent buildIdent reflect_base_beq in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_default...") in
        let base_default := cache_build_base_default base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building package...") in
        let exprInfo
            := constr:(@Classes.Build_ExprInfoT
                         base
                         ident
                         base_interp
                         ident_interp) in
        constr:(@GoalType.Build_package
                  exprInfo
                  (ltac:(
                     econstructor;
                     first [ exact base_default
                           | exact (@reflect_base_interp_beq)
                           | exact try_make_base_transport_cps_correct
                           | exact toFromRestrictedIdent
                           | exact buildInvertIdentCorrect
                           | exact (@buildInterpIdentCorrect)
                           | exact (@buildInterpEagerIdentCorrect)
                           | exact (@ident_interp_Proper) ]))
                  (@GoalType.Build_ExprReifyInfoT
                     exprInfo
                     all_base_and_interp
                     all_ident_and_interp)
                  ident_is_var_like).

      Ltac build_package_of_scraped scraped_data var_like_idents base ident :=
        lazymatch (eval hnf in scraped_data) with
        | {| ScrapedData.all_ident_named_interped := ?all_ident_named_interped
             ; ScrapedData.base_type_list_named := ?base_type_list_named |}
          => build_package base ident base_type_list_named var_like_idents all_ident_named_interped
        end.
      Ltac cache_build_package_of_scraped scraped_data var_like_idents base ident :=
        let name := fresh "package" in
        let term := build_package_of_scraped scraped_data var_like_idents base ident in
        cache_term term name.
Module Export Constr.
Import Ltac2.Constr.

Ltac2 is_sort(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Sort _ => true
  | _ => false
  end.
Module Export ProofsCommon.
Import Rewriter.Language.IdentifiersBasicLibrary.
Module Export Compilers.
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
Module Export Reify.
Import Coq.ZArith.ZArith.
Import Coq.FSets.FMapPositive.
Import Coq.MSets.MSetPositive.
Import Rewriter.Util.OptionList.
Local Set Default Proof Mode "Classic".
Module Export Compilers.
  Import invert_expr.
  Export Rewriter.Compilers.

  Module Export RewriteRules.
    Export Rewriter.Compilers.RewriteRules.

    Module Export Reify.
      Export Rewriter.Compilers.RewriteRules.Reify.
      Import Compile.
      Local Notation EvarMap_at base := (pattern.EvarMap_at base).

      Section with_var.
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
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
        Local Notation pattern := (@pattern.pattern base pident).
        Local Notation value := (@Compile.value base_type ident var).
        Local Notation UnderLets := (UnderLets.UnderLets base_type ident var).
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
          : @unification_resultT' (fun _ => positive) t p evm -> @unification_resultT' value t p evm -> PositiveMap.t { t : _ & value t } * (A -> list bool) -> PositiveMap.t { t : _ & value t } * (A -> list bool).
exact (match p return @unification_resultT' (fun _ => positive) _ p evm -> @unification_resultT' value _ p evm -> PositiveMap.t { t : _ & value t } * (A -> list bool) -> PositiveMap.t { t : _ & value t } * (A -> list bool) with
             | pattern.Wildcard t => fun p v '(m, l) => (PositiveMap.add p (existT value _ v) m, l)
             | pattern.Ident t idc => fun v1 v2 '(m, l) => (m, fun a => pident_type_of_list_arg_types_beq t idc v2 v1 :: l a)
             | pattern.App _ _ F X
               => fun x y '(m, l)
                  => let '(m, l) := @pair'_unification_resultT' _ _ _ F (fst x) (fst y) (m, l) in
                     let '(m, l) := @pair'_unification_resultT' _ _ _ X (snd x) (snd y) (m, l) in
                     (m, l)
             end).
Defined.

        Inductive expr_pos_to_expr_value_error_message :=
        | MISSING_VAR (_ : positive * type * PositiveMap.t { t : _ & value t })
        .
Fixpoint expr_pos_to_expr_value
                 (invalid : forall t, expr_pos_to_expr_value_error_message -> @expr.expr base_type ident value t)
                 {t} (e : @expr.expr base_type ident (fun _ => positive) t) (m : PositiveMap.t { t : _ & value t }) (cur_i : positive)
          : @expr.expr base_type ident value t.
exact (match e in expr.expr t return expr.expr t with
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
             end).
Defined.

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
          : { p : pattern (pattern.type.relax t) & @with_unif_rewrite_ruleTP_gen' _ p should_do_again true true evm }.
exact (let (p, unif_data_lhs) := @pattern_of_expr evm (fun _ => invalid _ _) t lhs in
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
                         else None)))).
Defined.

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

    Module Export Make.
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
          Local Notation pattern := (@pattern.pattern base pattern_ident).
          Local Notation pbase_type := (pattern.base.type base).
          Local Notation ptype := (type.type pbase_type).
          Let ptype_base {base} (t : pattern.base.type base) : type.type (pattern.base.type base) := type.base t.
Let ptype_base' (t : base) : pbase_type.
Admitted.
Let ptype_base'' (t : base) : ptype.
Admitted.
          Coercion ptype_base'' : base >-> ptype.
          Coercion ptype_base : pbase_type >-> ptype.
          Local Notation rewrite_ruleT := (@rewrite_ruleT base ident var pattern_ident (@arg_types)).
Definition make_base_Literal_pattern_folded (t : base) : pattern t.
Admitted.

          Context (pident_pair : forall A B : pbase_type, pattern_ident (A -> B -> A * B)%ptype).

          Context (cast_Literal_base_pattern_interp
                   : forall (evm : EvarMap) (t : base),
                      unification_resultT' (var:=var) (@arg_types) (make_base_Literal_pattern_folded t) evm
                      -> base.interp base_interp (pattern.base.subst_default (ptype_base' t) evm)).
Definition make_interp_rewrite'' {t} (idc : ident t) : option rewrite_ruleT.
Admitted.

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
Module Export RewriterBuildRegistry.
Ltac make_scraped_data_with_args := Basic.ScrapeTactics.make_scrape_data.
Ltac make_rules_proofs_with_args := Basic.ScrapeTactics.make_rules_proofsT_with_args.

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

  Goal ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args
       scraped_data InductiveHList.nil base ident raw_ident pattern_ident   false   false   true rules_proofs.

    Set Ltac Backtrace.
    Set Printing All.
    Set Printing Depth 100000000.
    let g := match goal with |- ?g => g end in
    let v :=
      constr:(
                ltac:(
                        idtac;
                        lazymatch g with
                        |                             @ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args
                              ?scraped_data ?var_like_idents ?base ?ident ?raw_ident
                              ?pattern_ident ?include_interp ?skip_early_reduction
                              ?skip_early_reduction_no_dtree _ ?specs_proofs =>
                            cbv[ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args];
                            let basic_package :=
                              IdentifiersBasicGenerate.Compilers.Basic.Tactic.cache_build_package_of_scraped
                                scraped_data var_like_idents base ident
                            in
                            let pattern_package :=
                              IdentifiersGenerate.Compilers.pattern.ident.Tactic.cache_build_package
                                basic_package raw_ident pattern_ident
                            in
                            let pkg_proofs :=
                              IdentifiersGenerateProofs.Compilers.pattern.ProofTactic.cache_build_package_proofs
                                basic_package pattern_package
                            in
                            let basic_package := (eval hnf in basic_package) in
                            let exprInfo :=
                              (eval hnf in
                                (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprInfo basic_package))
                            in
                            let exprExtraInfo :=
                              (eval hnf in
                                (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprExtraInfo basic_package))
                            in
                            let exprReifyInfo :=
                              (eval hnf in
                                (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprReifyInfo basic_package))
                            in
                            let ident_is_var_like :=
                              lazymatch basic_package
                              with
                              | IdentifiersBasicLibrary.Compilers.Basic.GoalType.Build_package _ _ _
                                                                                               ?ident_is_var_like => ident_is_var_like
                              end
                            in
                            let reify_package :=
                              IdentifiersBasicGenerate.Compilers.Basic.Tactic.reify_package_of_package
                                basic_package
                            in
                            let pkg_proofs_type := type of pkg_proofs in
                            let pkg :=
                              lazymatch (eval hnf in pkg_proofs_type)
                              with
                              | @IdentifiersLibraryProofs.Compilers.pattern.ProofGoalType.package_proofs
                                  ?base ?ident ?pkg => pkg
                              end
                            in
                            let specs := lazymatch type of specs_proofs
                                         with
                                         | @PrimitiveHList.hlist _ (@snd bool Prop) ?specs => specs
                                         | ?T =>
                                             let expected_type :=
                                               uconstr:((@PrimitiveHList.hlist _ (@snd bool Prop) ?[specs]))
                                             in
                                             ConstrFail.constr_fail_with
                                               ltac:(fun _ =>
                                                       fail 1 "Invalid type for specs_proofs:" T "Expected:" expected_type)
                                         end
                            in
                            let R_name := fresh "Rewriter_data" in
                            let pkg := eval hnf in pkg in
                            let rewriter_data := fresh "rewriter_data" in
                            let pkg_type := type of pkg in
                            let base :=
                              lazymatch (eval hnf in pkg_type)
                              with
                              | @IdentifiersLibrary.Compilers.pattern.ident.GoalType.package ?base ?ident =>
                                  base
                              end
                            in
                            let ident :=
                              lazymatch (eval hnf in pkg_type)
                              with
                              | @IdentifiersLibrary.Compilers.pattern.ident.GoalType.package ?base ?ident =>
                                  ident
                              end
                            in
                            let base_interp :=
                              lazymatch (eval hnf in exprInfo)
                              with
                              | Language.Compilers.Classes.Build_ExprInfoT _ _ ?base_interp _ =>
                                  base_interp
                              end
                            in
                            let try_make_transport_base_cps :=
                              lazymatch eval hnf in exprExtraInfo
                              with
                              | Language.Compilers.Classes.Build_ExprExtraInfoT _ _ _
                                                                                ?try_make_transport_base_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                                  try_make_transport_base_cps
                              end
                                in
                                let base_beq :=
                                  lazymatch eval hnf in exprExtraInfo
                                  with
                                  | Language.Compilers.Classes.Build_ExprExtraInfoT _
                                                                                    ?base_beq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => base_beq
                                  end
                                    in
                                    let invert_bind_args_unknown :=
                                      lazymatch eval hnf in pkg
                                      with
                                      | IdentifiersLibrary.Compilers.pattern.ident.GoalType.Build_package _ _ _ _ _ _
                                                                                                          _ _ _ _ _ _ _ _ _ _ _ ?v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => v
                                      end
                                        in
                                        let pident_unify_unknown :=
                                          lazymatch eval hnf in pkg
                                          with
                                          | IdentifiersLibrary.Compilers.pattern.ident.GoalType.Build_package _ _ _ _ _ _
                                                                                                              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                                                                              ?v => v
                                          end
                                            in
                                            let __ :=
                                              Rewriter.Compilers.RewriteRules.Make.debug1 ltac:(fun _ => idtac "Reifying...")
                                            in
                                            match goal with _ =>
                                                              idtac
   "let reify_package := constr:(" reify_package ") in
let exprInfo := constr:(" exprInfo ") in
let exprExtraInfo := constr:(" exprExtraInfo ") in
let pkg := constr:(" pkg ") in
let ident_is_var_like := constr:(" ident_is_var_like ") in
let include_interp := constr:(" include_interp ") in
let specs := constr:(" specs ") in
let reify_base :=
    IdentifiersBasicGenerate.Compilers.Basic.Tactic.reify_base_via_reify_package
     reify_package
   in
   let reify_ident :=
    IdentifiersBasicGenerate.Compilers.Basic.Tactic.reify_ident_via_reify_package
     reify_package
   in
   Reify.Compilers.RewriteRules.Make.Reify reify_base reify_ident exprInfo
    exprExtraInfo pkg ident_is_var_like include_interp specs
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
idtac v.";
                                                              exact_no_check  (
                                                                     let XXX := I in
let reify_package' := reify_package  in
let exprInfo' := exprInfo  in
let exprExtraInfo' := exprExtraInfo  in
let pkg' := pkg  in
let ident_is_var_like' := ident_is_var_like  in
let include_interp' := include_interp  in
let specs' := specs  in
I) end end) : True) in
    idtac "we could print out the term here with ""v"", but it's like 200kloc";
    lazymatch g with
                        |                             @ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args
                              ?scraped_data ?var_like_idents ?base ?ident ?raw_ident
                              ?pattern_ident ?include_interp ?skip_early_reduction
                              ?skip_early_reduction_no_dtree _ ?specs_proofs =>
                            cbv[ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args];
                            let basic_package :=
                              IdentifiersBasicGenerate.Compilers.Basic.Tactic.cache_build_package_of_scraped
                                scraped_data var_like_idents base ident
                            in
                            let pattern_package :=
                              IdentifiersGenerate.Compilers.pattern.ident.Tactic.cache_build_package
                                basic_package raw_ident pattern_ident
                            in
                            let pkg_proofs :=
                              IdentifiersGenerateProofs.Compilers.pattern.ProofTactic.cache_build_package_proofs
                                basic_package pattern_package
                            in
                            let basic_package := (eval hnf in basic_package) in
                            let exprInfo :=
                              (eval hnf in
                                (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprInfo basic_package))
                            in
                            let exprExtraInfo :=
                              (eval hnf in
                                (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprExtraInfo basic_package))
                            in
                            let exprReifyInfo :=
                              (eval hnf in
                                (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprReifyInfo basic_package))
                            in
                            let ident_is_var_like :=
                              lazymatch basic_package
                              with
                              | IdentifiersBasicLibrary.Compilers.Basic.GoalType.Build_package _ _ _
                                                                                               ?ident_is_var_like => ident_is_var_like
                              end
                            in
                            let reify_package :=
                              IdentifiersBasicGenerate.Compilers.Basic.Tactic.reify_package_of_package
                                basic_package
                            in
                            let pkg_proofs_type := type of pkg_proofs in
                            let pkg :=
                              lazymatch (eval hnf in pkg_proofs_type)
                              with
                              | @IdentifiersLibraryProofs.Compilers.pattern.ProofGoalType.package_proofs
                                  ?base ?ident ?pkg => pkg
                              end
                            in
                            let specs := lazymatch type of specs_proofs
                                         with
                                         | @PrimitiveHList.hlist _ (@snd bool Prop) ?specs => specs
                                         | ?T =>
                                             let expected_type :=
                                               uconstr:((@PrimitiveHList.hlist _ (@snd bool Prop) ?[specs]))
                                             in
                                             ConstrFail.constr_fail_with
                                               ltac:(fun _ =>
                                                       fail 1 "Invalid type for specs_proofs:" T "Expected:" expected_type)
                                         end
                            in
                            let R_name := fresh "Rewriter_data" in
                            let pkg := eval hnf in pkg in
                            let rewriter_data := fresh "rewriter_data" in
                            let pkg_type := type of pkg in
                            let base :=
                              lazymatch (eval hnf in pkg_type)
                              with
                              | @IdentifiersLibrary.Compilers.pattern.ident.GoalType.package ?base ?ident =>
                                  base
                              end
                            in
                            let ident :=
                              lazymatch (eval hnf in pkg_type)
                              with
                              | @IdentifiersLibrary.Compilers.pattern.ident.GoalType.package ?base ?ident =>
                                  ident
                              end
                            in
                            let base_interp :=
                              lazymatch (eval hnf in exprInfo)
                              with
                              | Language.Compilers.Classes.Build_ExprInfoT _ _ ?base_interp _ =>
                                  base_interp
                              end
                            in
                            let try_make_transport_base_cps :=
                              lazymatch eval hnf in exprExtraInfo
                              with
                              | Language.Compilers.Classes.Build_ExprExtraInfoT _ _ _
                                                                                ?try_make_transport_base_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                                  try_make_transport_base_cps
                              end
                                in
                                let base_beq :=
                                  lazymatch eval hnf in exprExtraInfo
                                  with
                                  | Language.Compilers.Classes.Build_ExprExtraInfoT _
                                                                                    ?base_beq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => base_beq
                                  end
                                    in
                                    let invert_bind_args_unknown :=
                                      lazymatch eval hnf in pkg
                                      with
                                      | IdentifiersLibrary.Compilers.pattern.ident.GoalType.Build_package _ _ _ _ _ _
                                                                                                          _ _ _ _ _ _ _ _ _ _ _ ?v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => v
                                      end
                                        in
                                        let pident_unify_unknown :=
                                          lazymatch eval hnf in pkg
                                          with
                                          | IdentifiersLibrary.Compilers.pattern.ident.GoalType.Build_package _ _ _ _ _ _
                                                                                                              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                                                                              ?v => v
                                          end
                                            in
                                            let __ :=
                                              Rewriter.Compilers.RewriteRules.Make.debug1 ltac:(fun _ => idtac "Reifying...")
                                            in
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
   idtac v end.

