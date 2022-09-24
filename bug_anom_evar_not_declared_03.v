(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+undeclared-scope,+deprecated-typeclasses-transparency-without-locality,unsupported-attributes" "-R" "src/Rewriter" "Rewriter" "-I" "src/Rewriter/Util/plugins" "-top" "Rewriter.Rewriter.Examples" "-native-compiler" "ondemand" "-native-compiler" "ondemand" "-native-compiler" "ondemand" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 104176 lines to 97527 lines, then from 97560 lines to 3537 lines, then from 3550 lines to 3708 lines, then from 3713 lines to 3598 lines, then from 46326 lines to 12572 lines, then from 12585 lines to 12752 lines, then from 12757 lines to 12574 lines, then from 12585 lines to 11970 lines, then from 11983 lines to 12141 lines, then from 12146 lines to 11971 lines, then from 11984 lines to 13915 lines, then from 13917 lines to 11971 lines, then from 11984 lines to 12981 lines, then from 12986 lines to 11971 lines, then from 11984 lines to 13016 lines, then from 13020 lines to 12051 lines, then from 12064 lines to 12309 lines, then from 12314 lines to 12056 lines, then from 12069 lines to 13696 lines, then from 13701 lines to 12072 lines, then from 12085 lines to 12681 lines, then from 12685 lines to 12083 lines, then from 12096 lines to 12395 lines, then from 12399 lines to 12085 lines, then from 12090 lines to 12086 lines *)
(* coqc version 8.15.0 compiled with OCaml 4.11.2
   coqtop version 8.15.0
   Expected coqc runtime on this file: 1.993 sec *)
Require Coq.ZArith.ZArith.

Module Export Prod.

Scheme Equality for prod.

Module Export Reflect.
Import Coq.Bool.Bool.

Existing Class reflect.
Notation reflect_rel P b := (forall x y, reflect (P x y) (b x y)).

Global Instance reflect_eq_unit : reflect_rel (@eq unit) (fun _ _ => true) | 10.
Admitted.
Global Instance reflect_eq_prod {A B eqA eqB} `{reflect_rel (@eq A) eqA, reflect_rel (@eq B) eqB} : reflect_rel (@eq (A * B)) (prod_beq A B eqA eqB) | 10.
Admitted.
Module Export Compilers.
  Local Set Boolean Equality Schemes.
  Module Export type.
    Inductive type {base_type : Type} := base (t : base_type) | arrow (s d : type).
    Global Arguments type : clear implicits.

    End type.
  Notation type := type.type.
  Module base.
    Module Export type.
      Inductive type {base_type : Type} := type_base (t : base_type) | prod (A B : type) | list (A : type) | option (A : type) | unit.
      Global Arguments type : clear implicits.
    End type.
    Notation type := type.type.
Definition reflect_type_beq {base} {base_beq} {r : reflect_rel (@eq base) base_beq}
      : reflect_rel (@eq (type base)) (@type.type_beq base base_beq).
Admitted.
  End base.
    Module Export PrimitiveSigma.
Module Import Primitive.
  Record sigT {A} P := existT { projT1 : A ; projT2 : P projT1 }.
  Global Arguments projT1 {_ _} _.
  Global Arguments projT2 {_ _} _.
    Notation "{ x : A  & P }" := (sigT (A:=A) (fun x => P)) : type_scope.

Module Export IdentifiersLibrary.
Import Coq.Lists.List.

Import EqNotations.
Module Export Compilers.

  Local Notation type_of_list := (fold_right (fun A B => prod A B) unit).

  Module Export pattern.
    Module Export Raw.
      Module Export ident.
        Inductive kind_of_type := GallinaType (_ : Type) | BaseBaseType | BaseType.
        Definition Type_of_kind_of_type (base : Type) (T : kind_of_type)
          := match T with
             | GallinaType T => T
             | BaseBaseType => base
             | BaseType => Compilers.base.type.type base
             end.

        Notation type_of_list_of_kind base ls
          := (type_of_list (List.map (@Type_of_kind_of_type base) ls)).

        Section with_base.
          Context {base : Type}.
          Local Notation ctype := (type.type (Compilers.base.type base)).
          Context {cident : ctype -> Type}.
          Local Notation type_of_list_of_kind ls := (type_of_list_of_kind base ls).

          Record preident_infos :=
            {
              dep_types : list Type;
              indep_types : list kind_of_type;
              indep_args : type_of_list dep_types -> list Type;
              to_type : forall d : type_of_list dep_types, type_of_list_of_kind indep_types -> Compilers.type (Compilers.base.type base);
              to_ident : forall (d : type_of_list dep_types) (i : type_of_list_of_kind indep_types), type_of_list (indep_args d) -> cident (to_type d i)
            }.

          Record ident_infos :=
            {
              preinfos :> preident_infos;
              dep_types_dec_transparent : forall x y : type_of_list (dep_types preinfos), {x = y} + {x <> y};
              indep_args_beq : _;
              indep_args_reflect
              : forall x, reflect_rel (@eq (type_of_list (indep_args preinfos x))) (indep_args_beq x);
              indep_types_beq : _;
              indep_types_reflect
              : reflect_rel (@eq (type_of_list_of_kind (indep_types preinfos))) indep_types_beq;
            }.

          Definition ident_args (pi : preident_infos)
            := { t : type_of_list (dep_types pi) & type_of_list_of_kind (indep_types pi) * type_of_list (indep_args pi t) }%type.

          Definition assemble_ident {pi} (args : ident_args pi)
            := to_ident pi (projT1 args) (Datatypes.fst (projT2 args)) (Datatypes.snd (projT2 args)).

          Section __.
            Context (ident : Set)
                    (all_idents : list ident)
                    (ident_index : ident -> nat)
                    (ident_index_idempotent : forall idc, List.nth_error all_idents (ident_index idc) = Some idc)
                    (eta_ident_cps_gen
                     : forall (T : ident -> Type)
                              (f : forall idc, T idc),
                        { f' : forall idc, T idc | forall idc, f' idc = f idc }).

            Context (ident_infos_of : ident -> ident_infos)
                    (split_ident_gen
                     : forall {t} (idc : cident t),
                        { ridc : ident & { args : ident_args (ident_infos_of ridc)
                                         | { pf : _ = _
                                           | idc = rew [cident] pf in assemble_ident args } } }).
Definition prefull_types : ident -> Type.
exact (fun idc => ident_args (ident_infos_of idc)).
Defined.
          End __.
        End with_base.

  Import Coq.ZArith.ZArith.
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

Definition base_interp0 : forall _ : base, Type .
exact (    fun ty : base =>
    match ty return Type with
    | base_Z => Z
    | base_nat0 => nat
    | base_bool0 => bool
    end).
Defined.
Definition base_beq0 : forall (_ : base) (_ : base), bool .
Admitted.
Definition reflect_base_beq0 :
    forall x y : base, Bool.reflect (@eq base x y) (base_beq0 x y) .
Admitted.
Definition base_interp_beq0 :
    forall (t1 t2 : base) (_ : base_interp0 t1) (_ : base_interp0 t2), bool .
Admitted.
Definition reflect_base_interp_beq0 :
    forall (t : base) (x y : base_interp0 t),
    Bool.reflect (@eq (base_interp0 t) x y) (base_interp_beq0 t t x y) .
Admitted.
Definition raw_ident_infos_of0 :
    forall _ : raw_ident,
    @IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_infos base ident .
exact (fun idc : raw_ident =>
    match
      idc
      return
        (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_infos base
           ident)
    with
    | raw_ident_false0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@nil
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)
             (fun _ : unit => @nil Type)
             (fun _ _ : unit =>
              @type.base (base.type.type base)
                (@base.type.type_base base base_bool0))
             (fun _ _ _ : unit => ident_false0))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (fun _ _ : unit => true) Reflect.reflect_eq_unit
    | raw_ident_flat_map =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit) i))
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i)))))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base)
                            (prod (base.type.type base) unit) i)))
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_flat_map
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_app =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@base.type.list base (@fst (base.type.type base) unit i)))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit i)))
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit i)))))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_app (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_map =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit) i))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base)
                            (prod (base.type.type base) unit) i)))
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_map
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_snd =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@base.type.prod base
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit) i)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.base (base.type.type base)
                   (@fst (base.type.type base) unit
                      (@snd (base.type.type base)
                         (prod (base.type.type base) unit) i))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_snd
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_fst =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@base.type.prod base
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit) i)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.base (base.type.type base)
                   (@fst (base.type.type base)
                      (prod (base.type.type base) unit) i)))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_fst
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_Z0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@nil
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)
             (fun _ : unit => @nil Type)
             (fun _ _ : unit =>
              @type.base (base.type.type base)
                (@base.type.type_base base base_Z))
             (fun _ _ _ : unit => ident_Z0))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (fun _ _ : unit => true) Reflect.reflect_eq_unit
    | raw_ident_add =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@nil
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)
             (fun _ : unit => @nil Type)
             (fun _ _ : unit =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@base.type.type_base base base_Z))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@base.type.type_base base base_Z))
                   (@type.base (base.type.type base)
                      (@base.type.type_base base base_Z))))
             (fun _ _ _ : unit => ident_add))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (fun _ _ : unit => true) Reflect.reflect_eq_unit
    | raw_ident_literal0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@cons Type base (@nil Type))
             (@nil
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)
             (fun d : prod base unit =>
              @cons Type
                match @fst base unit d return Type with
                | base_Z => Z
                | base_nat0 => nat
                | base_bool0 => bool
                end (@nil Type))
             (fun (d : prod base unit) (_ : unit) =>
              @type.base (base.type.type base)
                (@base.type.type_base base (@fst base unit d)))
             (fun (d : prod base unit) (_ : unit)
                (a : prod
                       match @fst base unit d return Type with
                       | base_Z => Z
                       | base_nat0 => nat
                       | base_bool0 => bool
                       end unit) =>
              ident_literal0 (@fst base unit d)
                (@fst
                   match @fst base unit d return Type with
                   | base_Z => Z
                   | base_nat0 => nat
                   | base_bool0 => bool
                   end unit a)))
          (fun x y : prod base unit =>
           match
             x as p
             return
               (forall x0 : prod base unit,
                sumbool (@eq (prod base unit) p x0)
                  (not (@eq (prod base unit) p x0)))
           with
           | pair a b =>
               fun x0 : prod base unit =>
               match
                 x0 as p
                 return
                   (sumbool (@eq (prod base unit) (@pair base unit a b) p)
                      (not (@eq (prod base unit) (@pair base unit a b) p)))
               with
               | pair a0 b0 =>
                   match
                     base_rec
                       (fun a1 : base =>
                        forall x1 : base,
                        sumbool (@eq base a1 x1) (not (@eq base a1 x1)))
                       (fun x1 : base =>
                        match
                          x1 as b1
                          return
                            (sumbool (@eq base base_Z b1)
                               (not (@eq base base_Z b1)))
                        with
                        | base_Z =>
                            @left (@eq base base_Z base_Z)
                              (not (@eq base base_Z base_Z))
                              (@eq_refl base base_Z)
                        | base_nat0 =>
                            @right (@eq base base_Z base_nat0)
                              (not (@eq base base_Z base_nat0))
                              (fun H2 : @eq base base_Z base_nat0 =>
                               False_ind False
                                 match
                                   H2 in (eq _ y0)
                                   return
                                     match y0 return Prop with
                                     | base_Z => True
                                     | base_nat0 => False
                                     | base_bool0 => False
                                     end
                                 with
                                 | eq_refl => I
                                 end)
                        | base_bool0 =>
                            @right (@eq base base_Z base_bool0)
                              (not (@eq base base_Z base_bool0))
                              (fun H2 : @eq base base_Z base_bool0 =>
                               False_ind False
                                 match
                                   H2 in (eq _ y0)
                                   return
                                     match y0 return Prop with
                                     | base_Z => True
                                     | base_nat0 => False
                                     | base_bool0 => False
                                     end
                                 with
                                 | eq_refl => I
                                 end)
                        end)
                       (fun x1 : base =>
                        match
                          x1 as b1
                          return
                            (sumbool (@eq base base_nat0 b1)
                               (not (@eq base base_nat0 b1)))
                        with
                        | base_Z =>
                            @right (@eq base base_nat0 base_Z)
                              (not (@eq base base_nat0 base_Z))
                              (fun H2 : @eq base base_nat0 base_Z =>
                               False_ind False
                                 match
                                   H2 in (eq _ y0)
                                   return
                                     match y0 return Prop with
                                     | base_Z => False
                                     | base_nat0 => True
                                     | base_bool0 => False
                                     end
                                 with
                                 | eq_refl => I
                                 end)
                        | base_nat0 =>
                            @left (@eq base base_nat0 base_nat0)
                              (not (@eq base base_nat0 base_nat0))
                              (@eq_refl base base_nat0)
                        | base_bool0 =>
                            @right (@eq base base_nat0 base_bool0)
                              (not (@eq base base_nat0 base_bool0))
                              (fun H2 : @eq base base_nat0 base_bool0 =>
                               False_ind False
                                 match
                                   H2 in (eq _ y0)
                                   return
                                     match y0 return Prop with
                                     | base_Z => False
                                     | base_nat0 => True
                                     | base_bool0 => False
                                     end
                                 with
                                 | eq_refl => I
                                 end)
                        end)
                       (fun x1 : base =>
                        match
                          x1 as b1
                          return
                            (sumbool (@eq base base_bool0 b1)
                               (not (@eq base base_bool0 b1)))
                        with
                        | base_Z =>
                            @right (@eq base base_bool0 base_Z)
                              (not (@eq base base_bool0 base_Z))
                              (fun H2 : @eq base base_bool0 base_Z =>
                               False_ind False
                                 match
                                   H2 in (eq _ y0)
                                   return
                                     match y0 return Prop with
                                     | base_Z => False
                                     | base_nat0 => False
                                     | base_bool0 => True
                                     end
                                 with
                                 | eq_refl => I
                                 end)
                        | base_nat0 =>
                            @right (@eq base base_bool0 base_nat0)
                              (not (@eq base base_bool0 base_nat0))
                              (fun H2 : @eq base base_bool0 base_nat0 =>
                               False_ind False
                                 match
                                   H2 in (eq _ y0)
                                   return
                                     match y0 return Prop with
                                     | base_Z => False
                                     | base_nat0 => False
                                     | base_bool0 => True
                                     end
                                 with
                                 | eq_refl => I
                                 end)
                        | base_bool0 =>
                            @left (@eq base base_bool0 base_bool0)
                              (not (@eq base base_bool0 base_bool0))
                              (@eq_refl base base_bool0)
                        end) a a0
                     return
                       (sumbool
                          (@eq (prod base unit) (@pair base unit a b)
                             (@pair base unit a0 b0))
                          (not
                             (@eq (prod base unit)
                                (@pair base unit a b)
                                (@pair base unit a0 b0))))
                   with
                   | left a1 =>
                       match
                         match
                           b as u
                           return
                             (forall x1 : unit,
                              sumbool (@eq unit u x1) (not (@eq unit u x1)))
                         with
                         | tt =>
                             fun x1 : unit =>
                             match
                               x1 as u
                               return
                                 (sumbool (@eq unit tt u)
                                    (not (@eq unit tt u)))
                             with
                             | tt =>
                                 @left (@eq unit tt tt)
                                   (not (@eq unit tt tt))
                                   (@eq_refl unit tt)
                             end
                         end b0
                         return
                           (sumbool
                              (@eq (prod base unit)
                                 (@pair base unit a b)
                                 (@pair base unit a0 b0))
                              (not
                                 (@eq (prod base unit)
                                    (@pair base unit a b)
                                    (@pair base unit a0 b0))))
                       with
                       | left a2 =>
                           @left
                             (@eq (prod base unit)
                                (@pair base unit a b)
                                (@pair base unit a0 b0))
                             (not
                                (@eq (prod base unit)
                                   (@pair base unit a b)
                                   (@pair base unit a0 b0)))
                             match
                               match
                                 a1 in (eq _ y0) return (@eq base y0 a)
                               with
                               | eq_refl => @eq_refl base a
                               end in (eq _ y0)
                               return
                                 (@eq (prod base unit)
                                    (@pair base unit y0 b)
                                    (@pair base unit a0 b0))
                             with
                             | eq_refl =>
                                 match
                                   match
                                     a2 in (eq _ y0) return (@eq unit y0 b)
                                   with
                                   | eq_refl => @eq_refl unit b
                                   end in (eq _ y0)
                                   return
                                     (@eq (prod base unit)
                                        (@pair base unit a0 y0)
                                        (@pair base unit a0 b0))
                                 with
                                 | eq_refl =>
                                     @eq_refl (prod base unit)
                                       (@pair base unit a0 b0)
                                 end
                             end
                       | right b1 =>
                           @right
                             (@eq (prod base unit)
                                (@pair base unit a b)
                                (@pair base unit a0 b0))
                             (not
                                (@eq (prod base unit)
                                   (@pair base unit a b)
                                   (@pair base unit a0 b0)))
                             match
                               match
                                 a1 in (eq _ y0) return (@eq base y0 a)
                               with
                               | eq_refl => @eq_refl base a
                               end in (eq _ y0)
                               return
                                 (not
                                    (@eq (prod base unit)
                                       (@pair base unit y0 b)
                                       (@pair base unit a0 b0)))
                             with
                             | eq_refl =>
                                 fun
                                   absurd : @eq (prod base unit)
                                              (@pair base unit a0 b)
                                              (@pair base unit a0 b0) =>
                                 b1
                                   (@f_equal (prod base unit) unit
                                      (fun e : prod base unit =>
                                       match e return unit with
                                       | pair _ u => u
                                       end) (@pair base unit a0 b)
                                      (@pair base unit a0 b0) absurd)
                             end
                       end
                   | right b1 =>
                       @right
                         (@eq (prod base unit) (@pair base unit a b)
                            (@pair base unit a0 b0))
                         (not
                            (@eq (prod base unit)
                               (@pair base unit a b)
                               (@pair base unit a0 b0)))
                         (fun
                            absurd : @eq (prod base unit)
                                       (@pair base unit a b)
                                       (@pair base unit a0 b0) =>
                          b1
                            (@f_equal (prod base unit) base
                               (fun e : prod base unit =>
                                match e return base with
                                | pair b2 _ => b2
                                end) (@pair base unit a b)
                               (@pair base unit a0 b0) absurd))
                   end
               end
           end y)
          (fun (x : prod base unit)
             (x0
              y : prod
                    match @fst base unit x return Type with
                    | base_Z => Z
                    | base_nat0 => nat
                    | base_bool0 => bool
                    end unit) =>
           Prod.prod_beq
             match @fst base unit x return Type with
             | base_Z => Z
             | base_nat0 => nat
             | base_bool0 => bool
             end unit
             (base_interp_beq0 (@fst base unit x) (@fst base unit x))
             (fun _ _ : unit => true) x0 y)
          (fun (x : prod base unit)
             (x0
              y : prod
                    match @fst base unit x return Type with
                    | base_Z => Z
                    | base_nat0 => nat
                    | base_bool0 => bool
                    end unit) =>
           @Reflect.reflect_eq_prod
             match @fst base unit x return Type with
             | base_Z => Z
             | base_nat0 => nat
             | base_bool0 => bool
             end unit
             (base_interp_beq0 (@fst base unit x) (@fst base unit x))
             (fun _ _ : unit => true)
             (reflect_base_interp_beq0 (@fst base unit x))
             Reflect.reflect_eq_unit x0 y) (fun _ _ : unit => true)
          Reflect.reflect_eq_unit
    | raw_ident_nil0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.base (base.type.type base)
                (@base.type.list base (@fst (base.type.type base) unit i)))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_nil0 (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_cons0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@fst (base.type.type base) unit i))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit i)))
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit i)))))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_cons0 (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_Some0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@fst (base.type.type base) unit i))
                (@type.base (base.type.type base)
                   (@base.type.option base
                      (@fst (base.type.type base) unit i))))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_Some0 (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_None0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.base (base.type.type base)
                (@base.type.option base (@fst (base.type.type base) unit i)))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_None0 (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_pair0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@fst (base.type.type base)
                      (prod (base.type.type base) unit) i))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i)))
                   (@type.base (base.type.type base)
                      (@base.type.prod base
                         (@fst (base.type.type base)
                            (prod (base.type.type base) unit) i)
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_pair0
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_tt0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@nil
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)
             (fun _ : unit => @nil Type)
             (fun _ _ : unit =>
              @type.base (base.type.type base) (@base.type.unit base))
             (fun _ _ _ : unit => ident_tt0))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (fun _ _ : unit => true) Reflect.reflect_eq_unit
    | raw_ident_prod_rect_nodep0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@cons
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                      (@nil
                         IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base)
                         (prod (base.type.type base)
                            (prod (base.type.type base) unit)) i))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base)
                            (prod (base.type.type base) unit)
                            (@snd (base.type.type base)
                               (prod (base.type.type base)
                                  (prod (base.type.type base) unit)) i)))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit)
                               (@snd (base.type.type base)
                                  (prod (base.type.type base)
                                     (prod (base.type.type base) unit)) i))))))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@base.type.prod base
                         (@fst (base.type.type base)
                            (prod (base.type.type base)
                               (prod (base.type.type base) unit)) i)
                         (@fst (base.type.type base)
                            (prod (base.type.type base) unit)
                            (@snd (base.type.type base)
                               (prod (base.type.type base)
                                  (prod (base.type.type base) unit)) i))))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit)
                            (@snd (base.type.type base)
                               (prod (base.type.type base)
                                  (prod (base.type.type base) unit)) i))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit)))
                (_ : unit) =>
              ident_prod_rect_nodep0
                (@fst (base.type.type base)
                   (prod (base.type.type base)
                      (prod (base.type.type base) unit)) i)
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   (@snd (base.type.type base)
                      (prod (base.type.type base)
                         (prod (base.type.type base) unit)) i))
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit)
                      (@snd (base.type.type base)
                         (prod (base.type.type base)
                            (prod (base.type.type base) unit)) i)))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) (prod (base.type.type base) unit))
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true))))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) (prod (base.type.type base) unit))
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true)))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true))
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                (@Reflect.reflect_eq_prod (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true)
                   (fun x y : base.type.type base =>
                    @base.reflect_type_beq base base_beq0 reflect_base_beq0 x
                      y) Reflect.reflect_eq_unit)))
    | raw_ident_bool_rect0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base) (@base.type.unit base))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit i)))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.unit base))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit i)))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_bool0))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit i)))))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_bool_rect0 (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_list_case0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base) (@base.type.unit base))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base)
                            (prod (base.type.type base) unit) i))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@base.type.list base
                               (@fst (base.type.type base)
                                  (prod (base.type.type base) unit) i)))
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit
                               (@snd (base.type.type base)
                                  (prod (base.type.type base) unit) i)))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.list base
                            (@fst (base.type.type base)
                               (prod (base.type.type base) unit) i)))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_list_case0
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_option_rect0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit) i))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.unit base))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.option base
                            (@fst (base.type.type base)
                               (prod (base.type.type base) unit) i)))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_option_rect0
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_nat_rect0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base) (@base.type.unit base))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit i)))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit i))
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit i))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit i)))))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_nat_rect0 (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_eager_nat_rect0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base) (@base.type.unit base))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit i)))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit i))
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit i))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit i)))))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_eager_nat_rect0 (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_nat_rect_arrow0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit) i))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.arrow (base.type.type base)
                         (@type.arrow (base.type.type base)
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base)
                                  (prod (base.type.type base) unit) i))
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base) unit
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base) unit) i))))
                         (@type.arrow (base.type.type base)
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base)
                                  (prod (base.type.type base) unit) i))
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base) unit
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base) unit) i))))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base)
                               (prod (base.type.type base) unit) i))
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit
                               (@snd (base.type.type base)
                                  (prod (base.type.type base) unit) i)))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_nat_rect_arrow0
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_eager_nat_rect_arrow0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit) i))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.arrow (base.type.type base)
                         (@type.arrow (base.type.type base)
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base)
                                  (prod (base.type.type base) unit) i))
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base) unit
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base) unit) i))))
                         (@type.arrow (base.type.type base)
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base)
                                  (prod (base.type.type base) unit) i))
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base) unit
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base) unit) i))))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base)
                               (prod (base.type.type base) unit) i))
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit
                               (@snd (base.type.type base)
                                  (prod (base.type.type base) unit) i)))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_eager_nat_rect_arrow0
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_list_rect0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base) (@base.type.unit base))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base)
                            (prod (base.type.type base) unit) i))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@base.type.list base
                               (@fst (base.type.type base)
                                  (prod (base.type.type base) unit) i)))
                         (@type.arrow (base.type.type base)
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base) unit
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base) unit) i)))
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base) unit
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base) unit) i))))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.list base
                            (@fst (base.type.type base)
                               (prod (base.type.type base) unit) i)))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_list_rect0
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_eager_list_rect0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@nil
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type)))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit)) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base) (@base.type.unit base))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit) i))))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base)
                            (prod (base.type.type base) unit) i))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@base.type.list base
                               (@fst (base.type.type base)
                                  (prod (base.type.type base) unit) i)))
                         (@type.arrow (base.type.type base)
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base) unit
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base) unit) i)))
                            (@type.base (base.type.type base)
                               (@fst (base.type.type base) unit
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base) unit) i))))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.list base
                            (@fst (base.type.type base)
                               (prod (base.type.type base) unit) i)))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit
                            (@snd (base.type.type base)
                               (prod (base.type.type base) unit) i))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base) unit))
                (_ : unit) =>
              ident_eager_list_rect0
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   i)
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit) i))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) unit)
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base) unit
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (fun _ _ : unit => true)
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                Reflect.reflect_eq_unit))
    | raw_ident_list_rect_arrow0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@cons
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                      (@nil
                         IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit)
                         (@snd (base.type.type base)
                            (prod (base.type.type base)
                               (prod (base.type.type base) unit)) i)))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit)
                            (@snd (base.type.type base)
                               (prod (base.type.type base)
                                  (prod (base.type.type base) unit)) i)))))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base)
                            (prod (base.type.type base)
                               (prod (base.type.type base) unit)) i))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@base.type.list base
                               (@fst (base.type.type base)
                                  (prod (base.type.type base)
                                     (prod (base.type.type base) unit)) i)))
                         (@type.arrow (base.type.type base)
                            (@type.arrow (base.type.type base)
                               (@type.base (base.type.type base)
                                  (@fst (base.type.type base)
                                     (prod (base.type.type base) unit)
                                     (@snd (base.type.type base)
                                        (prod (base.type.type base)
                                           (prod (base.type.type base) unit))
                                        i)))
                               (@type.base (base.type.type base)
                                  (@fst (base.type.type base) unit
                                     (@snd (base.type.type base)
                                        (prod (base.type.type base) unit)
                                        (@snd (base.type.type base)
                                           (prod (base.type.type base)
                                              (prod
                                                 (base.type.type base) unit))
                                           i)))))
                            (@type.arrow (base.type.type base)
                               (@type.base (base.type.type base)
                                  (@fst (base.type.type base)
                                     (prod (base.type.type base) unit)
                                     (@snd (base.type.type base)
                                        (prod (base.type.type base)
                                           (prod (base.type.type base) unit))
                                        i)))
                               (@type.base (base.type.type base)
                                  (@fst (base.type.type base) unit
                                     (@snd (base.type.type base)
                                        (prod (base.type.type base) unit)
                                        (@snd (base.type.type base)
                                           (prod (base.type.type base)
                                              (prod
                                                 (base.type.type base) unit))
                                           i))))))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.list base
                            (@fst (base.type.type base)
                               (prod (base.type.type base)
                                  (prod (base.type.type base) unit)) i)))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base)
                               (prod (base.type.type base) unit)
                               (@snd (base.type.type base)
                                  (prod (base.type.type base)
                                     (prod (base.type.type base) unit)) i)))
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit
                               (@snd (base.type.type base)
                                  (prod (base.type.type base) unit)
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base)
                                        (prod (base.type.type base) unit)) i))))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit)))
                (_ : unit) =>
              ident_list_rect_arrow0
                (@fst (base.type.type base)
                   (prod (base.type.type base)
                      (prod (base.type.type base) unit)) i)
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   (@snd (base.type.type base)
                      (prod (base.type.type base)
                         (prod (base.type.type base) unit)) i))
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit)
                      (@snd (base.type.type base)
                         (prod (base.type.type base)
                            (prod (base.type.type base) unit)) i)))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) (prod (base.type.type base) unit))
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true))))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) (prod (base.type.type base) unit))
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true)))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true))
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                (@Reflect.reflect_eq_prod (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true)
                   (fun x y : base.type.type base =>
                    @base.reflect_type_beq base base_beq0 reflect_base_beq0 x
                      y) Reflect.reflect_eq_unit)))
    | raw_ident_eager_list_rect_arrow0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@cons
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                   (@cons
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                      IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                      (@nil
                         IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))))
             (fun _ : unit => @nil Type)
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) =>
              @type.arrow (base.type.type base)
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base)
                         (prod (base.type.type base) unit)
                         (@snd (base.type.type base)
                            (prod (base.type.type base)
                               (prod (base.type.type base) unit)) i)))
                   (@type.base (base.type.type base)
                      (@fst (base.type.type base) unit
                         (@snd (base.type.type base)
                            (prod (base.type.type base) unit)
                            (@snd (base.type.type base)
                               (prod (base.type.type base)
                                  (prod (base.type.type base) unit)) i)))))
                (@type.arrow (base.type.type base)
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base)
                            (prod (base.type.type base)
                               (prod (base.type.type base) unit)) i))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@base.type.list base
                               (@fst (base.type.type base)
                                  (prod (base.type.type base)
                                     (prod (base.type.type base) unit)) i)))
                         (@type.arrow (base.type.type base)
                            (@type.arrow (base.type.type base)
                               (@type.base (base.type.type base)
                                  (@fst (base.type.type base)
                                     (prod (base.type.type base) unit)
                                     (@snd (base.type.type base)
                                        (prod (base.type.type base)
                                           (prod (base.type.type base) unit))
                                        i)))
                               (@type.base (base.type.type base)
                                  (@fst (base.type.type base) unit
                                     (@snd (base.type.type base)
                                        (prod (base.type.type base) unit)
                                        (@snd (base.type.type base)
                                           (prod (base.type.type base)
                                              (prod
                                                 (base.type.type base) unit))
                                           i)))))
                            (@type.arrow (base.type.type base)
                               (@type.base (base.type.type base)
                                  (@fst (base.type.type base)
                                     (prod (base.type.type base) unit)
                                     (@snd (base.type.type base)
                                        (prod (base.type.type base)
                                           (prod (base.type.type base) unit))
                                        i)))
                               (@type.base (base.type.type base)
                                  (@fst (base.type.type base) unit
                                     (@snd (base.type.type base)
                                        (prod (base.type.type base) unit)
                                        (@snd (base.type.type base)
                                           (prod (base.type.type base)
                                              (prod
                                                 (base.type.type base) unit))
                                           i))))))))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.list base
                            (@fst (base.type.type base)
                               (prod (base.type.type base)
                                  (prod (base.type.type base) unit)) i)))
                      (@type.arrow (base.type.type base)
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base)
                               (prod (base.type.type base) unit)
                               (@snd (base.type.type base)
                                  (prod (base.type.type base)
                                     (prod (base.type.type base) unit)) i)))
                         (@type.base (base.type.type base)
                            (@fst (base.type.type base) unit
                               (@snd (base.type.type base)
                                  (prod (base.type.type base) unit)
                                  (@snd (base.type.type base)
                                     (prod (base.type.type base)
                                        (prod (base.type.type base) unit)) i))))))))
             (fun (_ : unit)
                (i : prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit)))
                (_ : unit) =>
              ident_eager_list_rect_arrow0
                (@fst (base.type.type base)
                   (prod (base.type.type base)
                      (prod (base.type.type base) unit)) i)
                (@fst (base.type.type base) (prod (base.type.type base) unit)
                   (@snd (base.type.type base)
                      (prod (base.type.type base)
                         (prod (base.type.type base) unit)) i))
                (@fst (base.type.type base) unit
                   (@snd (base.type.type base)
                      (prod (base.type.type base) unit)
                      (@snd (base.type.type base)
                         (prod (base.type.type base)
                            (prod (base.type.type base) unit)) i)))))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base)
             (prod (base.type.type base) (prod (base.type.type base) unit))
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true))))
          (@Reflect.reflect_eq_prod (base.type.type base)
             (prod (base.type.type base) (prod (base.type.type base) unit))
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (Prod.prod_beq (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true)))
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             (@Reflect.reflect_eq_prod (base.type.type base)
                (prod (base.type.type base) unit)
                (fun x y : base.type.type base =>
                 base.type.type_beq base base_beq0 x y)
                (Prod.prod_beq (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true))
                (fun x y : base.type.type base =>
                 @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
                (@Reflect.reflect_eq_prod (base.type.type base) unit
                   (fun x y : base.type.type base =>
                    base.type.type_beq base base_beq0 x y)
                   (fun _ _ : unit => true)
                   (fun x y : base.type.type base =>
                    @base.reflect_type_beq base base_beq0 reflect_base_beq0 x
                      y) Reflect.reflect_eq_unit)))
    | raw_ident_List_nth_default0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@fst (base.type.type base) unit i))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit i)))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit i)))))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              => ident_List_nth_default0 (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    | raw_ident_eager_List_nth_default0 =>
        @IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_ident_infos
          base ident
          (@IdentifiersLibrary.Compilers.pattern.Raw.ident.Build_preident_infos
             base ident (@nil Type)
             (@cons
                IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type
                IdentifiersLibrary.Compilers.pattern.Raw.ident.BaseType
                (@nil
                   IdentifiersLibrary.Compilers.pattern.Raw.ident.kind_of_type))
             (fun _ : unit => @nil Type)
             (fun (_ : unit) (i : prod (base.type.type base) unit) =>
              @type.arrow (base.type.type base)
                (@type.base (base.type.type base)
                   (@fst (base.type.type base) unit i))
                (@type.arrow (base.type.type base)
                   (@type.base (base.type.type base)
                      (@base.type.list base
                         (@fst (base.type.type base) unit i)))
                   (@type.arrow (base.type.type base)
                      (@type.base (base.type.type base)
                         (@base.type.type_base base base_nat0))
                      (@type.base (base.type.type base)
                         (@fst (base.type.type base) unit i)))))
             (fun (_ : unit) (i : prod (base.type.type base) unit) (_ : unit)
              =>
              ident_eager_List_nth_default0
                (@fst (base.type.type base) unit i)))
          (fun x y : unit =>
           match
             x as u
             return
               (forall x0 : unit,
                sumbool (@eq unit u x0) (not (@eq unit u x0)))
           with
           | tt =>
               fun x0 : unit =>
               match
                 x0 as u
                 return (sumbool (@eq unit tt u) (not (@eq unit tt u)))
               with
               | tt =>
                   @left (@eq unit tt tt) (not (@eq unit tt tt))
                     (@eq_refl unit tt)
               end
           end y) (fun _ _ _ : unit => true)
          (fun _ : unit => Reflect.reflect_eq_unit)
          (Prod.prod_beq (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true))
          (@Reflect.reflect_eq_prod (base.type.type base) unit
             (fun x y : base.type.type base =>
              base.type.type_beq base base_beq0 x y)
             (fun _ _ : unit => true)
             (fun x y : base.type.type base =>
              @base.reflect_type_beq base base_beq0 reflect_base_beq0 x y)
             Reflect.reflect_eq_unit)
    end ).
Defined.
Ltac mk name ty body :=
  let __ := match goal with
            | _ => simple notypeclasses refine (let name : ty := _ in
                                                _);
                   [   transparent_abstract exact body using name
                   | ]
            end in
  lazymatch goal with
  | [ H := ?name |- _ ]
    => let __ := match goal with _ => clear H end in
       name
  end.
  Goal True.

  let raw_invert_bind_args0 := mk raw_invert_bind_args0 (
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
      end ) (
    fun (t : type.type (base.type.type base)) (idc : ident t)
      (pidc : raw_ident) =>
    match
      idc in (ident t0)
      return
        (option
           match pidc return Type with
           | raw_ident_false0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_false0
           | raw_ident_flat_map =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_flat_map
           | raw_ident_app =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_app
           | raw_ident_map =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_map
           | raw_ident_snd =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_snd
           | raw_ident_fst =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_fst
           | raw_ident_Z0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
           | raw_ident_add =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_add
           | raw_ident_literal0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_literal0
           | raw_ident_nil0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
           | raw_ident_cons0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
           | raw_ident_Some0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
           | raw_ident_None0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_None0
           | raw_ident_pair0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
           | raw_ident_tt0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
           | raw_ident_prod_rect_nodep0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_prod_rect_nodep0
           | raw_ident_bool_rect0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_bool_rect0
           | raw_ident_list_case0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_list_case0
           | raw_ident_option_rect0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_option_rect0
           | raw_ident_nat_rect0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0 raw_ident_nat_rect0
           | raw_ident_eager_nat_rect0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_eager_nat_rect0
           | raw_ident_nat_rect_arrow0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_nat_rect_arrow0
           | raw_ident_eager_nat_rect_arrow0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_eager_nat_rect_arrow0
           | raw_ident_list_rect0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_list_rect0
           | raw_ident_eager_list_rect0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_eager_list_rect0
           | raw_ident_list_rect_arrow0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_list_rect_arrow0
           | raw_ident_eager_list_rect_arrow0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_eager_list_rect_arrow0
           | raw_ident_List_nth_default0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_List_nth_default0
           | raw_ident_eager_List_nth_default0 =>
               @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                 base ident raw_ident raw_ident_infos_of0
                 raw_ident_eager_List_nth_default0
           end)
    with
    | ident_false0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod unit unit) tt
                 (@pair unit unit tt tt))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_flat_map t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_app t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_map t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_snd t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_fst t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_Z0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod unit unit) tt
                 (@pair unit unit tt tt))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_add =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod unit unit) tt
                 (@pair unit unit tt tt))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_literal0 t0 y =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
              (@PrimitiveSigma.Primitive.existT (prod base unit)
                 (fun t1 : prod base unit =>
                  prod unit
                    (prod
                       match @fst base unit t1 return Type with
                       | base_Z => Z
                       | base_nat0 => nat
                       | base_bool0 => bool
                       end unit)) (@pair base unit t0 tt)
                 (@pair unit
                    (prod
                       match
                         @fst base unit (@pair base unit t0 tt) return Type
                       with
                       | base_Z => Z
                       | base_nat0 => nat
                       | base_bool0 => bool
                       end unit) tt
                    (@pair
                       match
                         @fst base unit (@pair base unit t0 tt) return Type
                       with
                       | base_Z => Z
                       | base_nat0 => nat
                       | base_bool0 => bool
                       end unit y tt)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_nil0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_cons0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_Some0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_None0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_pair0 t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_tt0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod unit unit) tt
                 (@pair unit unit tt tt))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_prod_rect_nodep0 t0 t1 t2 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit)) t0
                       (@pair (base.type.type base)
                          (prod (base.type.type base) unit) t1
                          (@pair (base.type.type base) unit t2 tt))) tt))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_bool_rect0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_list_case0 t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_option_rect0 t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_nat_rect0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_eager_nat_rect0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_nat_rect_arrow0 t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_eager_nat_rect_arrow0 t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_list_rect0 t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_eager_list_rect0 t0 t1 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base) unit)) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base) unit) t0
                       (@pair (base.type.type base) unit t1 tt)) tt))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_list_rect_arrow0 t0 t1 t2 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit)) t0
                       (@pair (base.type.type base)
                          (prod (base.type.type base) unit) t1
                          (@pair (base.type.type base) unit t2 tt))) tt))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_eager_list_rect_arrow0 t0 t1 t2 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit =>
                  prod
                    (prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) unit) tt
                 (@pair
                    (prod (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit))) unit
                    (@pair (base.type.type base)
                       (prod (base.type.type base)
                          (prod (base.type.type base) unit)) t0
                       (@pair (base.type.type base)
                          (prod (base.type.type base) unit) t1
                          (@pair (base.type.type base) unit t2 tt))) tt))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_List_nth_default0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        | raw_ident_eager_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
        end
    | ident_eager_List_nth_default0 t0 =>
        match
          pidc as r
          return
            (option
               match r return Type with
               | raw_ident_false0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_false0
               | raw_ident_flat_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_flat_map
               | raw_ident_app =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_app
               | raw_ident_map =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_map
               | raw_ident_snd =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_snd
               | raw_ident_fst =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_fst
               | raw_ident_Z0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Z0
               | raw_ident_add =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_add
               | raw_ident_literal0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_literal0
               | raw_ident_nil0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_nil0
               | raw_ident_cons0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_cons0
               | raw_ident_Some0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_Some0
               | raw_ident_None0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_None0
               | raw_ident_pair0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_pair0
               | raw_ident_tt0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0 raw_ident_tt0
               | raw_ident_prod_rect_nodep0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_prod_rect_nodep0
               | raw_ident_bool_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_bool_rect0
               | raw_ident_list_case0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_case0
               | raw_ident_option_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_option_rect0
               | raw_ident_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect0
               | raw_ident_eager_nat_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect0
               | raw_ident_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_nat_rect_arrow0
               | raw_ident_eager_nat_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_nat_rect_arrow0
               | raw_ident_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect0
               | raw_ident_eager_list_rect0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect0
               | raw_ident_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_list_rect_arrow0
               | raw_ident_eager_list_rect_arrow0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_list_rect_arrow0
               | raw_ident_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_List_nth_default0
               | raw_ident_eager_List_nth_default0 =>
                   @IdentifiersLibrary.Compilers.pattern.Raw.ident.prefull_types
                     base ident raw_ident raw_ident_infos_of0
                     raw_ident_eager_List_nth_default0
               end)
        with
        | raw_ident_false0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_false0)))
        | raw_ident_flat_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_flat_map)))
        | raw_ident_app =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_app)))
        | raw_ident_map =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_map)))
        | raw_ident_snd =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_snd)))
        | raw_ident_fst =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_fst)))
        | raw_ident_Z0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Z0)))
        | raw_ident_add =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_add)))
        | raw_ident_literal0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_literal0)))
        | raw_ident_nil0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nil0)))
        | raw_ident_cons0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_cons0)))
        | raw_ident_Some0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_Some0)))
        | raw_ident_None0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_None0)))
        | raw_ident_pair0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_pair0)))
        | raw_ident_tt0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_tt0)))
        | raw_ident_prod_rect_nodep0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_prod_rect_nodep0)))
        | raw_ident_bool_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_bool_rect0)))
        | raw_ident_list_case0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_case0)))
        | raw_ident_option_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_option_rect0)))
        | raw_ident_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect0)))
        | raw_ident_eager_nat_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect0)))
        | raw_ident_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_nat_rect_arrow0)))
        | raw_ident_eager_nat_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_nat_rect_arrow0)))
        | raw_ident_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect0)))
        | raw_ident_eager_list_rect0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect0)))
        | raw_ident_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_list_rect_arrow0)))
        | raw_ident_eager_list_rect_arrow0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_list_rect_arrow0)))
        | raw_ident_List_nth_default0 =>
            @None
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_List_nth_default0)))
        | raw_ident_eager_List_nth_default0 =>
            @Some
              (@IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_args
                 base ident
                 (@IdentifiersLibrary.Compilers.pattern.Raw.ident.preinfos _
                    _ (raw_ident_infos_of0 raw_ident_eager_List_nth_default0)))
              (@PrimitiveSigma.Primitive.existT unit
                 (fun _ : unit => prod (prod (base.type.type base) unit) unit)
                 tt
                 (@pair (prod (base.type.type base) unit) unit
                    (@pair (base.type.type base) unit t0 tt) tt))
        end
    end ) in
  let invert_bind_args_unknown0 := mk invert_bind_args_unknown0 (
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
      end ) ( raw_invert_bind_args0 ) in idtac.
(*
Error: Anomaly "Evar ?X3577 was not declared."
Please report at http://coq.inria.fr/bugs/.
*)
