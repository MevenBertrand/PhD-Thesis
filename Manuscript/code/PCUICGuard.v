Inductive FixCoFix : Type := Fix | CoFix.

Axiom guard : FixCoFix -> global_env_ext -> context
      -> mfixpoint term -> Prop.

Definition fix_guard := guard Fix.
Definition cofix_guard := guard CoFix.