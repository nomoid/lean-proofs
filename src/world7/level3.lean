lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R :=
begin
    intros pq qr,
    cases pq with p q,
    cases qr with q r,
    split,
    {
        exact p,
    },
    {
        exact r,
    },
end