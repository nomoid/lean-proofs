example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
    intro f,
    intro g,
    intro p,
    have q := f p,
    apply q,
    apply g,
    exact p,
end
