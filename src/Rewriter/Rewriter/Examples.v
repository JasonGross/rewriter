(** * Examples of Using the Rewriter *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Util.LetIn.
Require Import Rewriter.Util.Notations.
Require Import Rewriter.Util.plugins.RewriterBuild.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Time Make norules := Rewriter For ().

(** Now we show some simple examples. *)

Example ex1 : forall x : nat, x = x.
Proof.
  Rewrite_for norules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

Example ex2 : forall x : nat, id x = id x.
Proof.
  Rewrite_for norules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

(** ==== *)

Local Ltac t :=
  repeat constructor; cbn [snd]; cbv [ident.eagerly]; intros;
  try solve [ lia
            | now apply ListUtil.eq_app_list_rect ].

Lemma map_eagerly_rect
  : forall A B f ls, @List.map A B f ls
                     = (ident.eagerly (@list_rect) _ _)
                         []
                         (fun x xs map_f_xs => f x :: map_f_xs)
                         ls.
Proof. t. Qed.

Lemma app_eagerly_rect
  : forall A xs ys, @List.app A xs ys
                    = (ident.eagerly (@list_rect) _ _)
                        ys (fun x xs app_xs_ys => x :: app_xs_ys) xs.
Proof. t. Qed.

Lemma flat_map_rect
  : forall A B f xs,
    @List.flat_map A B f xs
    = (list_rect (fun _ => _))
        nil
        (fun x _ flat_map_tl => f x ++ flat_map_tl)%list
        xs.
Proof. t. Qed.

Module ForDebugging.
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
          (* extra, can be anything whose subterms get added *) false).

  (*Rewriter Emit Inductives From Scraped scraped_data As base ident raw_ident pattern_ident.*)
  Import Language.Compilers.
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
       scraped_data InductiveHList.nil base ident raw_ident pattern_ident (* inlcude_interp: *) false (* skip_early_reduction: *) false (* skip_early_reduction_no_dtree: *) true rules_proofs.
    (* define everything *)
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
(* BUG:
Error:
Anomaly
"File "pretyping/evarsolve.ml", line 103, characters 9-15: Assertion failed."
Please report at http://coq.inria.fr/bugs/.
*)
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

    idtac.

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

idtac v." end in
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
  idtac
  in idtac in idtac in idtac end.

    let reify_package := constr:(
                                   (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprReifyInfo
                                      (IdentifiersBasicLibrary.Compilers.Basic.GoalType.Build_package
                                         (Language.Compilers.Classes.Build_ExprInfoT base ident base_interp0
                                                                                     ident_interp0)
                                         (Language.Compilers.Classes.Build_ExprExtraInfoT
                                            (Language.Compilers.Classes.Build_ExprInfoT base ident base_interp0
                                                                                        ident_interp0) base_beq0 base_interp_beq0 try_make_base_transport_cps0
                                            baseHasNat0 buildIdent0 toRestrictedIdent0 buildEagerIdent0 invertIdent0
                                            base_default0 reflect_base_beq0 reflect_base_interp_beq0
                                            try_make_base_transport_cps_correct0 baseHasNatCorrect0
                                            toFromRestrictedIdent0 buildInvertIdentCorrect0 buildInterpIdentCorrect0
                                            buildInterpEagerIdentCorrect0 ident_interp_Proper0)
                                         (IdentifiersBasicLibrary.Compilers.Basic.GoalType.Build_ExprReifyInfoT
                                            (Language.Compilers.Classes.Build_ExprInfoT base ident base_interp0
                                                                                        ident_interp0) all_base_and_interp0 all_ident_and_interp0)
                                         ident_is_var_like0)) ) in
    let exprInfo := constr:(
                              (Language.Compilers.Classes.Build_ExprInfoT base ident base_interp0 ident_interp0)
                            ) in
    let exprExtraInfo := constr:(
                                   (Language.Compilers.Classes.Build_ExprExtraInfoT
                                      (Language.Compilers.Classes.Build_ExprInfoT base ident base_interp0
                                                                                  ident_interp0) base_beq0 base_interp_beq0 try_make_base_transport_cps0
                                      baseHasNat0 buildIdent0 toRestrictedIdent0 buildEagerIdent0 invertIdent0
                                      base_default0 reflect_base_beq0 reflect_base_interp_beq0
                                      try_make_base_transport_cps_correct0 baseHasNatCorrect0 toFromRestrictedIdent0
                                      buildInvertIdentCorrect0 buildInterpIdentCorrect0 buildInterpEagerIdentCorrect0
                                      ident_interp_Proper0) ) in
    let pkg := constr:(
                         (IdentifiersLibrary.Compilers.pattern.ident.GoalType.Build_package base ident
                                                                                            all_base2 all_idents2 ident_index1 eta_ident_cps_gen2
                                                                                            eta_ident_cps_gen_expand_literal1 eta_ident_cps0 simple_idents0 raw_ident
                                                                                            all_raw_idents0 ident_index2 raw_ident_index_idempotent0 eta_ident_cps_gen3
                                                                                            raw_ident_infos_of0 split_raw_ident_gen0 raw_invert_bind_args0
                                                                                            invert_bind_args_unknown0 pattern_ident all_pattern_idents0 eta_ident_cps_gen4
                                                                                            eta_ident_cps_gen_expand_literal2 split_types0 add_types_from_raw_sig0
                                                                                            to_type_split_types_subst_default_eq0 projT1_add_types_from_raw_sig_eq0
                                                                                            arg_types_unfolded0 to_typed_unfolded0 type_of_list_arg_types_beq_unfolded0
                                                                                            of_typed_ident_unfolded0 arg_types_of_typed_ident_unfolded0 unify0
                                                                                            unify_unknown0) ) in
    let ident_is_var_like := constr:( ident_is_var_like0
                                    ) in
    let include_interp := constr:( false ) in
    let specs := constr:(
(@cons (prod bool Prop)
   (@pair bool Prop false (forall n : Z, @eq Z (Z.add n Z0) n))
   (@cons (prod bool Prop)
      (@pair bool Prop false
         (forall (A B : Type) (a : A) (b : B), @eq A (@fst A B (@pair A B a b)) a))
      (@cons (prod bool Prop)
         (@pair bool Prop false
            (forall (A B : Type) (a : A) (b : B),
             @eq B (@snd A B (@pair A B a b)) b))
         (@cons (prod bool Prop)
            (@pair bool Prop false
               (forall (A B : Type) (f : forall _ : A, B) (ls : list A),
                @eq (list B) (@map A B f ls)
                  (@PreCommon.Pre.ident.eagerly
                     (forall (A0 : Type) (P : forall _ : list A0, Type)
                        (_ : P (@nil A0))
                        (_ : forall (a : A0) (l : list A0) (_ : P l),
                             P (@cons A0 a l)) (l : list A0),
                      P l) list_rect A (fun _ : list A => list B)
                     (@nil B)
                     (fun (x : A) (_ : list A) (map_f_xs : list B) =>
                      @cons B (f x) map_f_xs) ls)))
            (@cons (prod bool Prop)
               (@pair bool Prop false
                  (forall (A : Type) (xs ys : list A),
                   @eq (list A) (@app A xs ys)
                     (@PreCommon.Pre.ident.eagerly
                        (forall (A0 : Type) (P : forall _ : list A0, Type)
                           (_ : P (@nil A0))
                           (_ : forall (a : A0) (l : list A0) (_ : P l),
                                P (@cons A0 a l)) (l : list A0),
                         P l) list_rect A (fun _ : list A => list A) ys
                        (fun (x : A) (_ app_xs_ys : list A) => @cons A x app_xs_ys)
                        xs)))
               (@cons (prod bool Prop)
                  (@pair bool Prop false
                     (forall (A P Q : Type) (N : forall _ : P, Q)
                        (C : forall (_ : A) (_ : list A)
                               (_ : forall _ : P, Q) (_ : P), Q)
                        (ls : list A) (v : P),
                      @eq Q (@list_rect_arrow_nodep A P Q N C ls v)
                        (@PreCommon.Pre.ident.eagerly
                           (forall (A0 P0 Q0 : Type) (_ : forall _ : P0, Q0)
                              (_ : forall (_ : A0) (_ : list A0)
                                     (_ : forall _ : P0, Q0)
                                     (_ : P0), Q0) (_ : list A0)
                              (_ : P0), Q0) (@list_rect_arrow_nodep) A P Q N C ls v)))
                  (@cons (prod bool Prop)
                     (@pair bool Prop false
                        (forall (A P : Type) (N : forall _ : unit, P)
                           (C : forall (_ : A) (_ : list A) (_ : P), P)
                           (ls : list A),
                         @eq P (@Thunked.list_rect A P N C ls)
                           (@PreCommon.Pre.ident.eagerly
                              (forall (A0 P0 : Type) (_ : forall _ : unit, P0)
                                 (_ : forall (_ : A0) (_ : list A0) (_ : P0), P0)
                                 (_ : list A0), P0) (@Thunked.list_rect) A P N C ls)))
                     (@cons (prod bool Prop)
                        (@pair bool Prop false
                           (forall (A P : Type) (N : forall _ : unit, P)
                              (C : forall (_ : A) (_ : list A), P),
                            @eq P (@Thunked.list_case A P N C (@nil A)) (N tt)))
                        (@cons (prod bool Prop)
                           (@pair bool Prop false
                              (forall (A P : Type) (N : forall _ : unit, P)
                                 (C : forall (_ : A) (_ : list A), P)
                                 (x : A) (xs : list A),
                               @eq P (@Thunked.list_case A P N C (@cons A x xs))
                                 (C x xs)))
                           (@cons (prod bool Prop)
                              (@pair bool Prop false
                                 (forall (A : Type) (default : A)
                                    (ls : list A) (n : nat),
                                  @eq A
                                    (@nth_default A default ls
                                       (@PreCommon.Pre.ident.literal nat n))
                                    (@PreCommon.Pre.ident.eagerly
                                       (forall (A0 : Type)
                                          (_ : A0) (_ : list A0)
                                          (_ : nat), A0) nth_default A default ls
                                       (@PreCommon.Pre.ident.literal nat n))))
                              (@cons (prod bool Prop)
                                 (@pair bool Prop true
                                    (forall (A B : Type)
                                       (f : forall _ : A, list B)
                                       (xs : list A),
                                     @eq (list B) (@flat_map A B f xs)
                                       (@list_rect A (fun _ : list A => list B)
                                          (@nil B)
                                          (fun (x : A)
                                             (_ : list A)
                                             (flat_map_tl : list B) =>
                                           @app B (f x) flat_map_tl) xs)))
                                 (@nil (prod bool Prop)))))))))))))
) in
    let reify_base :=     IdentifiersBasicGenerate.Compilers.Basic.Tactic.reify_base_via_reify_package      reify_package    in
    let reify_ident :=     IdentifiersBasicGenerate.Compilers.Basic.Tactic.reify_ident_via_reify_package      reify_package    in
    let __ := match goal with _ => idtac
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
idtac v." end in
    let v := Reify.Compilers.RewriteRules.Make.Reify reify_base reify_ident exprInfo     exprExtraInfo pkg ident_is_var_like include_interp specs in
    idtac v.


    Print Ltac AllTactics.Compilers.RewriteRules.Tactic.make_rewriter_from_scraped.
    Print Ltac AllTactics.Compilers.RewriteRules.Tactic.make_rewriter_via.
    Set Printing All.
    Print Ltac AllTactics.Compilers.RewriteRules.Build_Rewriter.
    Locate Ltac make_rewriter_via.
    Print Ltac Reify.Compilers.RewriteRules.Build_RewriterT.
    Print Ltac Reify.Compilers.RewriteRules.Make.Build_rewriter_dataT.
    idtac;
   lazymatch goal with
   | |-
     @ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args
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
  let res :=
   let basic_package := eval hnf in basic_package in
  let exprInfo :=
   eval hnf in
   (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprInfo basic_package)
  in
  let exprExtraInfo :=
   eval hnf in
   (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprExtraInfo basic_package)
  in
  let exprReifyInfo :=
   eval hnf in
   (IdentifiersBasicLibrary.Compilers.Basic.GoalType.exprReifyInfo basic_package)
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
   lazymatch eval hnf in pkg_proofs_type
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
  let R :=
   let pkg := eval hnf in pkg in
  let rewriter_data := fresh "rewriter_data" in
  let data :=
    let pkg_type := type of pkg in
  let base :=
   lazymatch eval hnf in pkg_type
   with
   | @IdentifiersLibrary.Compilers.pattern.ident.GoalType.package ?base ?ident =>
       base
   end
  in
  let ident :=
   lazymatch eval hnf in pkg_type
   with
   | @IdentifiersLibrary.Compilers.pattern.ident.GoalType.package ?base ?ident =>
       ident
   end
  in
  let base_interp :=
   lazymatch eval hnf in exprInfo
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
  let __ := match goal with _ => idtac
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
idtac v." end in idtac in idtac in idtac in idtac end.
  in
  idtac in idtac in idtac in idtac end.
  let dummy_count :=
   lazymatch specs_lems with
   | @pair _ _ (@pair _ _ ?n ?specs) ?lems => n
   end
  in
  let specs :=
   lazymatch specs_lems with
   | @pair _ _ (@pair _ _ ?n ?specs) ?lems => specs
   end
  in
  let rewrite_rules :=
   lazymatch specs_lems with
   | @pair _ _ (@pair _ _ ?n ?specs) ?lems => lems
   end
  in
  let rewrite_rules_names := fresh "rewrite_rules" in
  let rewrite_rules := CacheTerm.cache_term rewrite_rules rewrite_rules_names in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Compiling decision tree...")
  in
  let dtree :=
   Rewriter.Compilers.RewriteRules.Compile.CompileRewrites base ident
    (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.pattern_ident _ _ pkg)
    ((@IdentifiersLibrary.Compilers.pattern.ident.arg_types _ _
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of _
           _ pkg)
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.pattern_ident _ _ pkg)
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_pattern_ident_cps_gen
           _ _ pkg)
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.split_types _ _ pkg)))
    (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
    ((@IdentifiersLibrary.Compilers.pattern.ident.strip_types _ _
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of _
           _ pkg)
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.pattern_ident _ _ pkg)
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_pattern_ident_cps_gen
           _ _ pkg)
        (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.split_types _ _ pkg)))
    (IdentifiersLibrary.Compilers.pattern.Raw.ident.ident_beq
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_index _ _
          pkg)
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_raw_ident_cps_gen
          _ _ pkg)) rewrite_rules
  in
  let default_fuel := eval compute in (@length _ specs) in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Splitting rewrite rules...")
  in
  let split_rewrite_rules :=
   Reify.Compilers.RewriteRules.Make.AdjustRewriteRulesForReduction.make_split_rewrite_rules
    rewrite_rules
  in
  let pr1_rewrite_rules :=
   Reify.Compilers.RewriteRules.Make.AdjustRewriteRulesForReduction.make_pr1_rewrite_rules
    split_rewrite_rules
  in
  let pr2_rewrite_rules :=
   Reify.Compilers.RewriteRules.Make.AdjustRewriteRulesForReduction.make_pr2_rewrite_rules
    split_rewrite_rules
  in
  let all_rewrite_rules :=
   Reify.Compilers.RewriteRules.Make.AdjustRewriteRulesForReduction.make_all_rewrite_rules
    pkg pr1_rewrite_rules pr2_rewrite_rules
  in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Assembling rewrite_head...")
  in
  let rewrite_head0 := fresh "rewrite_head0" in
  let var := fresh "var" in
  let rewrite_head0 :=
   CacheTerm.cache_term
    (fun var =>
     @Rewriter.Compilers.RewriteRules.Compile.assemble_identifier_rewriters base
       (@Language.Compilers.Classes.try_make_transport_base_cps exprInfo
          exprExtraInfo)
       (@Language.Compilers.Classes.base_beq exprInfo exprExtraInfo) ident var
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_ident_cps _ _ pkg)
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.pattern_ident _ _ pkg)
       ((@IdentifiersLibrary.Compilers.pattern.ident.arg_types _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.pattern_ident _ _
              pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_pattern_ident_cps_gen
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.split_types _ _
              pkg)))
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.unify _ _ pkg)
       pident_unify_unknown
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
       ((@IdentifiersLibrary.Compilers.pattern.Raw.ident.full_types _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_raw_ident_cps_gen
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg)))
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.invert_bind_args _ _
          pkg) invert_bind_args_unknown
       ((@IdentifiersLibrary.Compilers.pattern.Raw.ident.type_of _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_raw_ident_cps_gen
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg)))
       ((@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_typed _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_raw_ident_cps_gen
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg)))
       ((@IdentifiersLibrary.Compilers.pattern.Raw.ident.is_simple _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg))) (@Some _ dtree) (all_rewrite_rules var)) rewrite_head0
  in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Reducing rewrite_head...")
  in
  let rewrite_head :=
   Reify.Compilers.RewriteRules.Make.make_rewrite_head base_interp
    try_make_transport_base_cps base_beq ident pident_unify_unknown
    invert_bind_args_unknown skip_early_reduction rewrite_head0 pr2_rewrite_rules
  in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Assembling rewrite_head_no_dtree...")
  in
  let rewrite_head_no_dtree0 := fresh "rewrite_head_no_dtree0" in
  let var := fresh "var" in
  let rewrite_head_no_dtree0 :=
   CacheTerm.cache_term
    (fun var =>
     @Rewriter.Compilers.RewriteRules.Compile.assemble_identifier_rewriters base
       (@Language.Compilers.Classes.try_make_transport_base_cps exprInfo
          exprExtraInfo)
       (@Language.Compilers.Classes.base_beq exprInfo exprExtraInfo) ident var
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_ident_cps _ _ pkg)
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.pattern_ident _ _ pkg)
       ((@IdentifiersLibrary.Compilers.pattern.ident.arg_types _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.pattern_ident _ _
              pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_pattern_ident_cps_gen
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.split_types _ _
              pkg)))
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.unify _ _ pkg)
       pident_unify_unknown
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
       ((@IdentifiersLibrary.Compilers.pattern.Raw.ident.full_types _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_raw_ident_cps_gen
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg)))
       (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.invert_bind_args _ _
          pkg) invert_bind_args_unknown
       ((@IdentifiersLibrary.Compilers.pattern.Raw.ident.type_of _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_raw_ident_cps_gen
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg)))
       ((@IdentifiersLibrary.Compilers.pattern.Raw.ident.to_typed _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.eta_raw_ident_cps_gen
              _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg)))
       ((@IdentifiersLibrary.Compilers.pattern.Raw.ident.is_simple _ _
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident _ _ pkg)
           (@IdentifiersLibrary.Compilers.pattern.ident.GoalType.raw_ident_infos_of
              _ _ pkg))) (@None _) (all_rewrite_rules var)) rewrite_head_no_dtree0
  in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Reducing rewrite_head_no_dtree...")
  in
  let rewrite_head_no_dtree :=
   Reify.Compilers.RewriteRules.Make.make_rewrite_head base_interp
    try_make_transport_base_cps base_beq ident pident_unify_unknown
    invert_bind_args_unknown skip_early_reduction_no_dtree rewrite_head_no_dtree0
    pr2_rewrite_rules
  in
  constr:((Rewriter.Compilers.RewriteRules.Make.GoalType.Build_rewriter_dataT'
             exprInfo exprExtraInfo pkg ident_is_var_like specs dummy_count dtree
             rewrite_rules all_rewrite_rules (@eq_refl _ _) default_fuel
             rewrite_head (@eq_refl _ _) rewrite_head_no_dtree
             (@eq_refl _ _)))
  in
  idtac in idtac in idtac end.
  end.
  let R := CacheTerm.cache_term R R_name in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Proving Rewriter_Wf...")
  in
  let Rwf := fresh "Rewriter_Wf" in
  let Rwf :=
   CacheTerm.cache_proof_with_type_by
    (@ProofsCommon.Compilers.RewriteRules.WfTactics.GoalType.Wf_GoalT exprInfo
       exprExtraInfo pkg R)
    ltac:(idtac;
           ProofsCommonTactics.Compilers.RewriteRules.WfTactics.Tactic.prove_good
            ltac:(())) Rwf
  in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Proving Rewriter_Interp...")
  in
  let RInterp := fresh "Rewriter_Interp" in
  let RInterp :=
   CacheTerm.cache_proof_with_type_by
    (@ProofsCommon.Compilers.RewriteRules.InterpTactics.GoalType.Interp_GoalT
       exprInfo exprExtraInfo pkg R)
    ltac:(idtac;
           ProofsCommonTactics.Compilers.RewriteRules.InterpTactics.Tactic.prove_interp_good
            ltac:(())) RInterp
  in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Assembling verified rewriter...")
  in
  AllTactics.Compilers.RewriteRules.make_VerifiedRewriter exprInfo exprExtraInfo
   exprReifyInfo pkg pkg_proofs R Rwf RInterp specs_proofs

  in
  let __ :=
   Rewriter.Compilers.RewriteRules.Make.debug1
    ltac:(fun _ => idtac "Refining with verified rewriter...")
  in
  refine
  res
   end.
    Set Printing All.
    Print AllTactics.Compilers.RewriteRules.Tactic.make_rewriter_all.
    Print RewriterBuildRegistry.make_verified_rewriter_with_args.
    RewriterBuildRegistry.make_verified_rewriter_with_args.
  Definition myrules :=
    (ltac:(RewriterBuildRegistry.make_verified_rewriter_with_args)
      : ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args
          scraped_data InductiveHList.nil base ident raw_ident pattern_ident (* inlcude_interp: *) false (* skip_early_reduction: *) false (* skip_early_reduction_no_dtree: *) true rules_proofs).
End ForDebugging.

Time Make myrules
  := Rewriter For (Z.add_0_r
                   , (@Prod.fst_pair)
                   , (@Prod.snd_pair)
                   , map_eagerly_rect
                   , app_eagerly_rect
                   , eval_rect list
                   , do_again flat_map_rect).

(** Now we show some simple examples. *)

Example ex3 : forall x, x + 0 = x.
Proof.
  Rewrite_for myrules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

Ltac test_rewrite :=
  Rewrite_for myrules;
  lazymatch goal with
  | [ |- ?x = ?y ] => first [ constr_eq x y; idtac "Success:" x; reflexivity
                            | fail 1 x "≢" y ]
  end.

Example ex4 : forall y e1 e2,
    map (fun x => y + x) (dlet z := e1 + e2 in [0; 1; 2; z; z+1])
    = dlet z := e1 + e2 in [y; y + 1; y + 2; y + z; y + (z + 1)].
Proof. test_rewrite. Qed.

Example ex5 : forall (x1 x2 x3 : Z),
    flat_map (fun a => [a; a; a]) [x1;x2;x3]
    = [x1; x1; x1; x2; x2; x2; x3; x3; x3].
Proof. test_rewrite. Qed.
