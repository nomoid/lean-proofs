import world6.level8

lemma contra (P Q : Prop) : P ∧ ¬ P → Q :=
begin
    intro h,
    exfalso,
    cases h with p np,
    rw not_iff_imp_false at np,
    apply np,
    exact p,
end