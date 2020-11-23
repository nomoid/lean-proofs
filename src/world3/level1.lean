import mynat.definition
import mynat.mul

namespace mynat

lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin [nat_num_game]
    induction m with d hd,
    {
        rw mul_zero,
        refl,
    },
    {
        rw mul_succ,
        rw add_zero,
        exact hd,
    },
end

end mynat