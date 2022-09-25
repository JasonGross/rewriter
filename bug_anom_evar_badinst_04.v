(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,-undeclared-scope,+deprecated-typeclasses-transparency-without-locality,unsupported-attributes,-deprecated-native-compiler-option,-require-in-module" "-R" "src/Rewriter" "Rewriter" "-I" "src/Rewriter/Util/plugins" "-top" "Rewriter.Rewriter.Examples" "-native-compiler" "ondemand" "-native-compiler" "ondemand" "-native-compiler" "ondemand" "-native-compiler" "ondemand" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 104176 lines to 97527 lines, then from 97560 lines to 3537 lines, then from 3550 lines to 3708 lines, then from 3713 lines to 3538 lines, then from 3551 lines to 3718 lines, then from 3723 lines to 3540 lines, then from 3553 lines to 3711 lines, then from 3716 lines to 3542 lines, then from 3555 lines to 3711 lines, then from 3716 lines to 3574 lines, then from 3587 lines to 7609 lines, then from 7612 lines to 3623 lines, then from 3636 lines to 5049 lines, then from 5052 lines to 4422 lines, then from 4435 lines to 4464 lines, then from 4469 lines to 4430 lines, then from 4441 lines to 4298 lines, then from 4311 lines to 6242 lines, then from 6245 lines to 4519 lines, then from 4533 lines to 4556 lines, then from 4562 lines to 4519 lines, then from 4533 lines to 5529 lines, then from 5535 lines to 5240 lines, then from 5254 lines to 5295 lines, then from 5301 lines to 5250 lines, then from 5264 lines to 5298 lines, then from 5304 lines to 5263 lines, then from 5277 lines to 5317 lines, then from 5323 lines to 5280 lines, then from 5294 lines to 5326 lines, then from 5332 lines to 5282 lines, then from 5296 lines to 5327 lines, then from 5333 lines to 5283 lines, then from 5297 lines to 5332 lines, then from 5338 lines to 5295 lines, then from 5301 lines to 5296 lines, then from 5987 lines to 5485 lines, then from 5487 lines to 5359 lines, then from 5365 lines to 5360 lines *)
(* coqc version 8.15.0 compiled with OCaml 4.11.2
   coqtop version 8.15.0
   Modules that could not be inlined: Rewriter.Rewriter.Rewriter
   Expected coqc runtime on this file: 1.751 sec *)
Require Ltac2.Ltac2.
Require Rewriter.Rewriter.Rewriter.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export Ident.
Import Ltac2.Ltac2.
Import Ltac2.Printf.

Ltac2 of_constr (refine_to_named_lambda : Ltac1.t -> unit) (c : constr) : ident
  := let default () := Control.throw (Tactic_failure (Some (fprintf "Ident.of_constr: failure to make a name from %t" c))) in
     match Constr.Unsafe.kind '(ltac2:(refine_to_named_lambda (Ltac1.of_constr c))) with
     | Constr.Unsafe.Lambda x _
       => match Constr.Binder.name x with
          | Some id => id
          | None => default ()
          end
     | _ => default ()
     end.
Module Export Char.
Ltac2 newline () : char := Char.of_int 10.
Module Export String.
Ltac2 newline () : string := String.make 1 (Char.newline ()).
Module Export Message.

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

Module Export Option.
  Ltac2 equal (eq : 'a -> 'b -> bool) (a : 'a option) (b : 'b option) : bool
    := match a with
       | None => match b with
                 | None => true
                 | _ => false
                 end
       | Some a => match b with
                   | Some b => eq a b
                   | _ => false
                   end
       end.

Module Export Array.
  Import Ltac2.Array.
  Ltac2 rec for_all2_aux (p : 'a -> 'b -> bool) (a : 'a array) (b : 'b array) (pos : int) (len : int) :=
    if Int.equal len 0
    then true
    else if p (get a pos) (get b pos)
         then for_all2_aux p a b (Int.add pos 1) (Int.sub len 1)
         else false.
  Ltac2 equal p a b :=
    let lena := length a in
    let lenb := length b in
    if Int.equal lena lenb
    then for_all2_aux p a b 0 lena
    else false.
End Array.

Module Export Projection.
  Ltac2 equal (x : projection) (y : projection) : bool
    := let dummy := make (Rel (-1)) in
       Constr.equal (make (Proj x dummy)) (make (Proj y dummy)).

Module Export Constr.
  Import Ltac2.Constr.
  Import Ltac2.Bool.
  Ltac2 rec kind_nocast_gen kind (x : constr) :=
    let k := kind x in
    match k with
    | Cast x _ _ => kind_nocast_gen kind x
    | _ => k
    end.
  Ltac2 rec equal_nounivs (x : constr) (y : constr) : bool :=
    let kind := kind_nocast_gen kind in
    if Constr.equal x y
    then true
    else match kind x with
         | Cast x _ _ => equal_nounivs x y
         | App fx xs
           => match kind y with
              | App fy ys
                => equal_nounivs fx fy
                   && Array.equal equal_nounivs xs ys
              | _ => false
              end
         | Rel _ => false
         | Var _ => false
         | Meta _ => false
         | Uint63 _ => false
         | Float _ => false
         | Evar ex instx
           => match kind y with
              | Evar ey insty
                => let inst := Array.empty () in
                   if Constr.equal (make (Evar ex inst)) (make (Evar ey inst))
                   then Array.equal equal_nounivs instx insty
                   else false
              | _ => false
              end
         | Sort sx
           => match kind y with
              | Sort sy => true
              | _ => false
              end
         | Prod xb fx
           => match kind y with
              | Prod yb fy
                => equal_nounivs (Binder.type xb) (Binder.type yb) && equal_nounivs fx fy
              | _ => false
              end
         | Lambda xb fx
           => match kind y with
              | Lambda yb fy
                => equal_nounivs (Binder.type xb) (Binder.type yb) && equal_nounivs fx fy
              | _ => false
              end
         | LetIn xb xv fx
           => match kind y with
              | LetIn yb yv fy
                => equal_nounivs (Binder.type xb) (Binder.type yb) && equal_nounivs xv yv && equal_nounivs fx fy
              | _ => false
              end
         | Constant cx instx
           => match kind y with
              | Constant cy insty
                => Constr.equal (make (Constant cx instx)) (make (Constant cy instx))
              | _ => false
              end
         | Ind ix instx
           => match kind y with
              | Ind iy insty
                => Ind.equal ix iy
              | _ => false
              end
         | Constructor cx instx
           => match kind y with
              | Constructor cy insty
                => Constr.equal (make (Constructor cx instx)) (make (Constructor cy instx))
              | _ => false
              end
         | Fix xa xi xb xf
           => match kind y with
              | Fix ya yi yb yf
                => Array.equal Int.equal xa ya
                   && Int.equal xi yi
                   && Array.equal (fun b1 b2 => equal_nounivs (Binder.type b1) (Binder.type b2)) xb yb
                   && Array.equal equal_nounivs xf yf
              | _ => false
              end
         | CoFix xi xb xf
           => match kind y with
              | CoFix yi yb yf
                => Int.equal xi yi
                   && Array.equal (fun b1 b2 => equal_nounivs (Binder.type b1) (Binder.type b2)) xb yb
                   && Array.equal equal_nounivs xf yf
              | _ => false
              end
         | Proj px cx
           => match kind y with
              | Proj py cy
                => Projection.equal px py && equal_nounivs cx cy
              | _ => false
              end
         | Array _ x1 x2 x3
           => match kind y with
              | Array _ y1 y2 y3
                => Array.equal equal_nounivs x1 y1
                   && equal_nounivs x2 y2
                   && equal_nounivs x3 y3
              | _ => false
              end
         | Case cx x1 cix x2 x3
           => match kind y with
              | Case cy y1 ciy y2 y3
                => Option.equal (Array.equal equal_nounivs)
                                (match cix with
                                 | NoInvert => None
                                 | CaseInvert cix => Some cix
                                 end)
                                (match cix with
                                 | NoInvert => None
                                 | CaseInvert ciy => Some ciy
                                 end)
                   && equal_nounivs x1 y1
                   && equal_nounivs x2 y2
                   && Array.equal equal_nounivs x3 y3
              | _ => false
              end
         end.

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
           List.assoc_opt Constr.equal_nounivs term cache.
      Ltac2 Type exn ::= [ Cache_contains_element (constr, constr, constr, elem) ].
      Ltac2 add (head_constant : constr) (term : constr) (rterm : constr) (cache : t) : ident
        := let (avoid, known) := cache.(contents) in
           match List.assoc_opt Constr.equal_nounivs term known with
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
                    if Constr.equal_nounivs c '@Let_In
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
Module Export IdentifiersBasicGenerate.
Module Export Compilers.

  Module Export Basic.
    Export IdentifiersBasicLibrary.Compilers.Basic.

    Module Import Tactics.

      Ltac2 reify_base_via_list_opt (base : constr) (base_interp : constr) (all_base_and_interp : constr) :=
        let all_base_and_interp := Std.eval_hnf all_base_and_interp in
        let all_base_and_interp := Std.eval_cbv (strategy:(beta)) all_base_and_interp in
        fun ty
        => let ty := Std.eval_cbv (strategy:(beta)) ty in
           Reify.debug_enter_reify "reify_base_via_list" ty;
           let rty := match! all_base_and_interp with
                      | context[Datatypes.cons (?rty, ?ty')]
                        => if Constr.equal_nounivs ty ty'
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
                 => if Constr.equal_nounivs base_interp' base_interp
                    then Some t
                    else Control.zero Match_failure
               | @base.interp ?base' ?base_interp' (@base.type.type_base ?base' ?t)
                 => if Constr.equal_nounivs base_interp' base_interp && Constr.equal_nounivs base base
                    then Some t
                    else Control.zero Match_failure
               | @type.interp (base.type ?base') (@base.interp ?base' ?base_interp') (@Compilers.type.base (base.type ?base') (@base.type.type_base ?base' ?t))
                 => if Constr.equal_nounivs base_interp' base_interp && Constr.equal_nounivs base base
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

      Ltac2 rec is_recursively_constructor_or_literal (term : constr) : bool :=
        match Constr.Unsafe.kind term with
        | Constr.Unsafe.Cast term _ _ => is_recursively_constructor_or_literal term
        | Constr.Unsafe.App f args
          => if Constr.equal_nounivs f '@ident.literal
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
          => if Constr.equal_nounivs ident_interp ident_interp'
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
                                            => if Constr.equal_nounivs idc idc'
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
                                            => if Constr.equal_nounivs idc idc'
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
    End Tactics.

    Module Export Tactic.
      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
      Ltac reify_base_via_reify_package := Tactics.reify_base_via_reify_package.
      #[deprecated(since="8.15",note="Use Ltac2 instead.")]
      Ltac reify_ident_via_reify_package := Tactics.reify_ident_via_reify_package.
Module Export Constr.

Ltac2 is_sort(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Sort _ => true
  | _ => false
  end.
Module Export Reify.
Import Coq.ZArith.ZArith.
Import Coq.FSets.FMapPositive.
Import Coq.MSets.MSetPositive.
Import Coq.Lists.List.
Import Rewriter.Util.OptionList.
Import Rewriter.Util.Bool.Reflect.
Import Rewriter.Util.Tactics.ConstrFail.
Import Rewriter.Util.Tactics.Head.
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
                              let t :=   (mkApp base_type_interp [mkApp '@pattern.base.lookup_default ['(ltac:(repeat match goal with H : _ |- _ => clear H end)); cur_i; ty_ctx] ]) in
                              printf "3";
                              let p :=   (Constr.Unsafe.substnl [t] 0 p) in
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

      Ltac check_exact val :=
        lazymatch goal with
        | _
          => lazymatch val with
             | ?f ?x
               => check_exact f; check_exact x
             | fun x : ?T => ?f
               => let f' := fresh in
                  check_exact T;
                  let __ := constr:(fun x : T
                                    => match f return _ with
                                       | f' => ltac:(let f := (eval cbv delta [f'] in f') in
                                                     clear f';
                                                     check_exact f;
                                                     exact I)
                                       end) in
                  idtac
             | _ => idtac
             end;
             idtac "checking:" val;
             tryif (let __ := constr:(ltac:(exact val)) in
                    idtac)
             then idtac
             else (let val' := (eval cbv beta in val) in
                   idtac "β:" val';
                   let __ := constr:(ltac:(repeat match goal with H : _ |- _ => clear H end; exact val)) in
                   idtac)
        end.

      Ltac equation_to_parts' lem side_conditions :=
        let __ := match goal with _ => idtac "equation_to_parts'" lem side_conditions end in
        lazymatch lem with
        | ?H -> ?P
          => let __ := match goal with _ => idtac H "->" P end in
             let __ := lazymatch type of H with
                       | Prop => constr:(I)
                       | ?T => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-Prop non-dependent hypothesis of type" H ":" T "when reifying a lemma of type" lem)
                       end in
             let __ := match goal with _ => idtac "prop_to_bool" H end in
             let H := prop_to_bool H in
             let __ := match goal with _ => idtac "push_side_conditions" H side_conditions end in
             let side_conditions := push_side_conditions H side_conditions in
             equation_to_parts' P side_conditions
        | forall x : ?T, ?P
          => let __ := match goal with _ => idtac "forall" end in
             let P' := fresh in
             constr:(
               fun x : T
               => match P return _ with
                  | P'
                    => ltac:(let __ := match goal with _ => idtac "P':" P' end in
                             let P := (eval cbv delta [P'] in P') in
                             let __ := match goal with _ => idtac "P:" P end in
                             clear P';
                             let res := equation_to_parts' P side_conditions in
                             let __ := match goal with _ => idtac "eq res:" res end in
                             let __ := match goal with _ => check_exact res end in
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
          => let __ := match goal with _ => idtac "cont:" ty_ctx cur_i lem end in
             let lem := equation_to_parts lem in
             let __ := match goal with _ => idtac "reify_to_pattern_and_replacement_in_context" base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota ty_ctx var gets_inlined should_do_again "constr:(1%positive)" lem "(@expr.var_context.nil (base.type base) (fun _ => positive)" end in
             let res := reify_to_pattern_and_replacement_in_context base reify_base base_interp base_interp_beq try_make_transport_base_cps ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota ty_ctx var gets_inlined should_do_again constr:(1%positive) lem (@expr.var_context.nil (base.type base) (fun _ => positive)) in
             let __ := match goal with _ => idtac "reify under res:" res end in
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
admit.
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
admit.
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
Goal True.
  Unset Ltac Backtrace.

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
