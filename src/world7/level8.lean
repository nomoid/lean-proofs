lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
begin
    intro pqr,
    cases pqr with p qr,
    cases qr with q r,
    {
        left,
        split,
        {
            exact p,
        },
        {
            exact q,
        },
    },
    {
        right,
        split,
        {
            exact p,
        },
        {
            exact r,
        }
    }
end