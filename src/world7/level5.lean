lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
    intros pq qr,
    split,
    {
        intro p,
        apply qr.1,
        apply pq.1,
        exact p,
    },
    {
        intro r,
        apply pq.2,
        apply qr.2,
        exact r,
    },
end

lemma iff_trans_2 (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
    intros pq qr,
    rw pq,
    rw qr,
end