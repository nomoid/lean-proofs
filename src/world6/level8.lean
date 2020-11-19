lemma not_iff_imp_false (P : Prop) : ¬ P ↔ P → false := iff.rfl

example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
    repeat {rw not_iff_imp_false},
    intros pq qf p,
    apply qf,
    apply pq,
    exact p,
end