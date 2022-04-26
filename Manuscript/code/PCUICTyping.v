Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel : forall n decl,
  wf_local Σ Γ ->
  nth_error Γ n = Some decl ->
  Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)
| type_Sort : forall s,
  wf_local Σ Γ ->
  wf_universe Σ s ->
  Σ ;;; Γ |- tSort s : tSort (super s)
| type_Prod : forall na A B s1 s2,
  Σ ;;; Γ |- A : tSort s1 ->
  Σ ;;; Γ ,, vass na A |- B : tSort s2 ->
  Σ ;;; Γ |- tProd na A B : tSort (sort_of_product s1 s2)
| type_Lambda : forall na A t s1 B,
  Σ ;;; Γ |- A : tSort s1 ->
  Σ ;;; Γ ,, vass na A |- t : B ->
  Σ ;;; Γ |- tLambda na A t : tProd na A B
| type_App : forall t na A B s u,
  Σ ;;; Γ |- tProd na A B : tSort s ->
  Σ ;;; Γ |- t : tProd na A B ->
  Σ ;;; Γ |- u : A ->
  Σ ;;; Γ |- tApp t u : B{0 := u}
| type_LetIn : forall na b B t s1 A,
  Σ ;;; Γ |- B : tSort s1 ->
  Σ ;;; Γ |- b : B ->
  Σ ;;; Γ ,, vdef na b B |- t : A ->
  Σ ;;; Γ |- tLetIn na b B t : tLetIn na b B A
| type_Const : forall cst u decl,
  wf_local Σ Γ ->
  declared_constant Σ cst decl ->
  consistent_instance_ext Σ decl.(cst_universes) u ->
  Σ ;;; Γ |- tConst cst u : decl.(cst_type)@[u]
| type_Ind : forall ind u mdecl idecl,
  wf_local Σ Γ ->
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ mdecl.(ind_universes) u ->
  Σ ;;; Γ |- tInd ind u : idecl.(ind_type)@[u]
| type_Construct : forall ind i u mdecl idecl cdecl,
  wf_local Σ Γ ->
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  consistent_instance_ext Σ mdecl.(ind_universes) u ->
  Σ ;;; Γ |- tConstruct ind i u : type_of_constructor mdecl cdecl (ind, i) u
| type_Case : forall ci p c brs indices ps mdecl idecl,
  let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  declared_inductive Σ ci.(ci_ind) mdecl idecl ->
  Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
  Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
  case_side_conditions (fun Σ Γ => wf_local Σ Γ) typing Σ Γ ci p ps
                        mdecl idecl indices predctx  ->
  case_branch_typing (fun Σ Γ => wf_local Σ Γ) typing Σ Γ ci p ps
                      mdecl idecl ptm brs ->
  Σ ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])
| type_Proj : forall p c u mdecl idecl cdecl pdecl args,
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
  #|args| = ind_npars mdecl ->
  Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (snd pdecl)@[u]
| type_Fix : forall mfix n decl,
  wf_local Σ Γ ->
  fix_guard Σ Γ mfix ->
  nth_error mfix n = Some decl ->
  All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
  All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) :
            lift0 #|fix_context mfix| d.(dtype))) mfix ->
  wf_fixpoint Σ mfix ->
  Σ ;;; Γ |- tFix mfix n : decl.(dtype)
| type_CoFix : forall mfix n decl,
  wf_local Σ Γ ->
  cofix_guard Σ Γ mfix ->
  nth_error mfix n = Some decl ->
  All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
  All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) :
            lift0 #|fix_context mfix| d.(dtype)) mfix ->
  wf_cofixpoint Σ mfix ->
  Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)
| type_Cumul : forall t A B s,
  Σ ;;; Γ |- t : A ->
  Σ ;;; Γ |- B : tSort s ->
  Σ ;;; Γ |- A <=s B ->
  Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T)
and "'wf_local' Σ Γ " := (All_local_env (lift_typing typing Σ) Γ).