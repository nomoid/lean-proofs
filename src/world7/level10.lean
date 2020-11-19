import world7.level1
import world7.level9

local attribute [instance, priority 10] classical.prop_decidable

lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
begin
    by_cases p : P; by_cases q : Q,
    {
        intros nqnp p,
        exact q,
    },
    {
        intro nqnp,
        have np := nqnp q,
        have pnp := (both_and P ¬ P) p np,
        have q := (contra P Q) pnp,
        intro p,
        exact q,
    },
    {
        intros nqnp p,
        exact q,
    },
    {
        intro nqnp,
        intro yp,
        have pnp := (both_and P ¬ P) yp p,
        have q := (contra P Q) pnp,
        exact q,
    },
end