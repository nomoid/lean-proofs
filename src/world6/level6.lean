example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
    intro f,
    intro g,
    intro p,
    apply f,
    {
        exact p,
    },
    {
        apply g,
        exact p,
    }
end
