import mynat.definition
import mynat.mul
import world2.level2

namespace mynat

lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b :=
begin [nat_num_game]
    induction b with d hd,
    {
        rw add_zero,
        rw mul_zero,
        rw add_zero,
        refl,
    },
    {
        rw add_succ,
        rw mul_succ,
        rw hd,
        rw mul_succ,
        rw add_assoc,
        refl,
    },
end

end mynat