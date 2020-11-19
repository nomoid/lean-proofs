example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) :=
begin
    intro pq,
    intro qf,
    intro p,
    apply qf,
    apply pq,
    exact p,
end
