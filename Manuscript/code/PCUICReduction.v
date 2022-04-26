Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
(** Reductions *)
| red_beta na t b a : 
  Σ ;;; Γ |- tApp (tLambda na t b) a ~> b {0 := a}

| red_zeta na b t b' :
  Σ ;;; Γ |- tLetIn na b t b' ~> b' {0 := b}
…
(** Congruences*)
| app_red_l M1 N1 M2 : Σ ;;; Γ |- M1 ~> N1 -> Σ ;;; Γ |- tApp M1 M2 ~> tApp N1 M2
| app_red_r M2 N2 M1 : Σ ;;; Γ |- M2 ~> N2 -> Σ ;;; Γ |- tApp M1 M2 ~> tApp M1 N2
…
where " Σ ;;; Γ |- t ~> u " := (red1 Σ Γ t u).

Definition red Σ Γ := clos_refl_trans (fun t u : term => Σ;;; Γ |- t ~> u).