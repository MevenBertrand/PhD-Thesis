Inductive cumulSpec0 {cf : checker_flags} (Σ : global_env_ext) Γ (pb : conv_pb)
  : term -> term -> Type :=
| cumul_Trans : forall t u v,
  is_closed_context Γ -> is_open_term Γ u -> 
  Σ ;;; Γ ⊢ t ≤s[pb] u ->
  Σ ;;; Γ ⊢ u ≤s[pb] v ->    
  Σ ;;; Γ ⊢ t ≤s[pb] v 
| cumul_Sym : forall t u, 
  Σ ;;; Γ ⊢ t ≤s[Conv] u ->
  Σ ;;; Γ ⊢ u ≤s[pb] t  
| cumul_Refl : forall t,
  Σ ;;; Γ ⊢ t ≤s[pb] t

(* Cumulativity rules *)
| cumul_Ind : forall i u u' args args', 
  cumul_Ind_univ Σ pb i #|args| u u' ->
  All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
  Σ ;;; Γ ⊢ mkApps (tInd i u) args ≤s[pb] mkApps (tInd i u') args'
| cumul_Construct : forall i k u u' args args',
  cumul_Construct_univ Σ pb i k #|args| u u' ->
  All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
  Σ ;;; Γ ⊢ mkApps (tConstruct i k u) args
     ≤s[pb] mkApps (tConstruct i k u') args'
| cumul_Sort : forall s s',
  compare_universe pb Σ s s' ->
  Σ ;;; Γ ⊢ tSort s ≤s[pb] tSort s'
| cumul_Const : forall c u u',
  R_universe_instance (compare_universe Conv Σ) u u' ->
  Σ ;;; Γ ⊢ tConst c u ≤s[pb] tConst c u'

(* congruence rules *)
| cumul_Evar : forall e args args', 
  All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
  Σ ;;; Γ ⊢ tEvar e args ≤s[pb] tEvar e args'
| cumul_App : forall t t' u u', 
  Σ ;;; Γ ⊢ t ≤s[pb] t' ->
  Σ ;;; Γ ⊢ u ≤s[Conv] u' ->
  Σ ;;; Γ ⊢ tApp t u ≤s[pb] tApp t' u'
| cumul_Lambda : forall na na' ty ty' t t',
  eq_binder_annot na na' ->
  Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
  Σ ;;; Γ ,, vass na ty ⊢ t ≤s[pb] t' ->
  Σ ;;; Γ ⊢ tLambda na ty t ≤s[pb] tLambda na' ty' t'
| cumul_Prod : forall na na' a a' b b',
  eq_binder_annot na na' ->
  Σ ;;; Γ ⊢ a ≤s[Conv] a' ->
  Σ ;;; Γ ,, vass na a ⊢ b ≤s[pb] b' ->
  Σ ;;; Γ ⊢ tProd na a b ≤s[pb] tProd na' a' b'
| cumul_LetIn : forall na na' t t' ty ty' u u', 
  eq_binder_annot na na' ->
  Σ ;;; Γ ⊢ t ≤s[Conv] t' ->
  Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
  Σ ;;; Γ ,, vdef na t ty ⊢ u ≤s[pb] u' ->
  Σ ;;; Γ ⊢ tLetIn na t ty u ≤s[pb] tLetIn na' t' ty' u'
| cumul_Case indn : forall p p' c c' brs brs', 
  cumul_predicate (fun Γ t u => Σ ;;; Γ ⊢ t ≤s[Conv] u)
      Γ (compare_universe Conv Σ) p p' ->
  Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
  All2 (fun br br' =>
    eq_context_gen eq eq (bcontext br) (bcontext br') × 
    Σ ;;; Γ ,,, inst_case_branch_context p br ⊢ bbody br ≤s[Conv] bbody br'
  ) brs brs' ->
  Σ ;;; Γ ⊢ tCase indn p c brs ≤s[pb] tCase indn p' c' brs'
| cumul_Proj : forall p c c', 
  Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
  Σ ;;; Γ ⊢ tProj p c ≤s[pb] tProj p c'
| cumul_Fix : forall mfix mfix' idx,
  All2 (fun x y =>
    Σ ;;; Γ ⊢ x.(dtype) ≤s[Conv] y.(dtype) ×
    Σ ;;; Γ ,,, fix_context mfix ⊢ x.(dbody) ≤s[Conv] y.(dbody) ×
    (x.(rarg) = y.(rarg)) ×
    eq_binder_annot x.(dname) y.(dname)
  ) mfix mfix' ->
  Σ ;;; Γ ⊢ tFix mfix idx ≤s[pb] tFix mfix' idx
| cumul_CoFix : forall mfix mfix' idx,
  All2 (fun x y =>
    Σ ;;; Γ ⊢ x.(dtype) ≤s[Conv] y.(dtype) ×
    Σ ;;; Γ ,,, fix_context mfix ⊢ x.(dbody) ≤s[Conv] y.(dbody) ×
    (x.(rarg) = y.(rarg)) ×
    eq_binder_annot x.(dname) y.(dname)
  ) mfix mfix' ->
  Σ ;;; Γ ⊢ tCoFix mfix idx ≤s[pb] tCoFix mfix' idx

(** Reductions *)

(** Beta and iota red *)
| cumul_beta : forall na t b a,
  Σ ;;; Γ ⊢ tApp (tLambda na t b) a ≤s[pb] b {0 := a}
| cumul_iota : forall ci c u args p brs br, 
  nth_error brs c = Some br ->
  #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
  Σ ;;; Γ ⊢ tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs  ≤s[pb]
      iota_red ci.(ci_npar) p args br
| cumul_proj : forall p args u arg,
  nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
  Σ ;;; Γ ⊢ tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args) ≤s[pb] arg

(** Definitions *)
| cumul_zeta : forall na b t b',
  Σ ;;; Γ ⊢ tLetIn na b t b' ≤s[pb] b' {0 := b}
| cumul_rel i body :
  option_map decl_body (nth_error Γ i) = Some (Some body) ->
  Σ ;;; Γ ⊢ tRel i ≤s[pb] lift0 (S i) body
| cumul_delta : forall c decl body (isdecl : declared_constant Σ c decl) u,
  decl.(cst_body) = Some body ->
  Σ ;;; Γ ⊢ tConst c u ≤s[pb] body@[u]

(** Fix unfolding, with guard *)
| cumul_fix : forall mfix idx args narg fn,
  unfold_fix mfix idx = Some (narg, fn) ->
  is_constructor narg args = true ->
  Σ ;;; Γ ⊢ mkApps (tFix mfix idx) args ≤s[pb] mkApps fn args
| cumul_cofix_case : forall ip p mfix idx args narg fn brs,
  unfold_cofix mfix idx = Some (narg, fn) ->
  Σ ;;; Γ ⊢ tCase ip p (mkApps (tCoFix mfix idx) args) brs 
     ≤s[pb] tCase ip p (mkApps fn args) brs
| cumul_cofix_proj : forall p mfix idx args narg fn,
  unfold_cofix mfix idx = Some (narg, fn) ->
  Σ ;;; Γ ⊢ tProj p (mkApps (tCoFix mfix idx) args)
     ≤s[pb] tProj p (mkApps fn args)

where " Σ ;;; Γ ⊢ t ≤s[ pb ] u " := (@cumulSpec0 _ Σ Γ pb t u) : type_scope.

Definition convSpec `{checker_flags} (Σ : global_env_ext) Γ :=
    cumulSpec0 Σ Γ Conv.
Definition cumulSpec `{checker_flags} (Σ : global_env_ext) Γ :=
    cumulSpec0 Σ Γ Cumul.