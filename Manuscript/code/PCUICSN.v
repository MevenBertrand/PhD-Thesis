Axiom normalisation :
wf_ext Σ ->
forall Γ t,
  welltyped Σ Γ t ->
  Acc (cored Σ Γ) t.