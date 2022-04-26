Inductive typing_result_comp (A : Type) : Type :=
  | Checked_comp : A -> typing_result_comp A
  | TypeError_comp : type_error -> (A -> False) ->
      typing_result_comp A.

Equations infer
  (Γ : context)
  (HΓ : forall Σ (wfΣ : abstract_env_ext_rel X Σ), || wf_local Σ Γ ||)
  (t : term)
  : typing_result_comp ({ A : term &
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), || Σ ;;; Γ |- t |> A || })
  by struct t :=

  infer Γ HΓ (tRel n)
    with inspect (nth_error Γ n) := {
    | exist (Some c) e => ret ((lift0 (S n)) (decl_type c); _) ;
    | exist None e => raise (UnboundRel n)
    } ;

  infer Γ HΓ (tVar n) := raise (UnboundVar n) ;

  infer Γ HΓ (tEvar ev _) := raise (UnboundEvar ev) ;

  infer Γ HΓ (tSort u) with inspect (abstract_env_wf_universeb _ X u) := {
    | exist true _ := ret (tSort (Universe.super u);_) ;
    | exist false _ := raise
        (Msg ("Sort contains an undeclared level " ^ string_of_sort u))
  } ;

  infer Γ HΓ (tProd na A B) :=
    s1 <- infer_type  infer Γ HΓ A ;;
    s2 <- infer_type infer (Γ,,vass na A) _ B ;;
    Checked_comp (tSort (Universe.sort_of_product s1.π1 s2.π1);_) ;

  infer Γ HΓ (tLambda na A t) :=
    infer_type infer Γ HΓ A ;;
    B <- infer (Γ ,, vass na A) _ t ;;
    ret (tProd na A B.π1; _);

  infer Γ HΓ (tLetIn n b b_ty b') :=
    infer_type infer Γ HΓ b_ty ;;
    bdcheck infer Γ HΓ b b_ty _ ;;
    b'_ty <- infer (Γ ,, vdef n b b_ty) _ b' ;;
    ret (tLetIn n b b_ty b'_ty.π1; _) ;

  infer Γ HΓ (tApp t u) :=
    ty <- infer Γ HΓ t ;;
    pi <- reduce_to_prod (X_type := X_type) Γ ty.π1 _ ;;
    bdcheck infer Γ HΓ u pi.π2.π1 _ ;;
    ret (subst10 u pi.π2.π2.π1; _) ;

…