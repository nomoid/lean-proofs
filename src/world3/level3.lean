import mynat.definition
import mynat.mul
import world2.level5

namespace mynat

lemma one_mul (m : mynat) : 1 * m = m :=
begin [nat_num_game]
    induction m with d hd,
    {
        rw mul_zero,
        refl,
    },
    {
        rw mul_succ,
        rw succ_eq_add_one,
        rw hd,
        refl,
    },
end

end mynat