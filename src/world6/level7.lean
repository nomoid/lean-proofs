example (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) :=
begin
    intros pq qf p,
    apply qf,
    apply pq,
    exact p,
end
