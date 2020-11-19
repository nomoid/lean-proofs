lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
    intros pq qr,
    cases pq with hpq hqp,
    cases qr with hqr hrq,
    split,
    {
        intro p,
        apply hqr,
        apply hpq,
        exact p,
    },
    {
        intro r,
        apply hqp,
        apply hrq,
        exact r,
    },
end