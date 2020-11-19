example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) :=
begin
    intro pq,
    intro qf,
    intro p,
    apply qf,
    apply pq,
    exact p,
end
