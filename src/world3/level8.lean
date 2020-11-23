import mynat.definition
import mynat.mul
import world3.level1
import world3.level6

namespace mynat

lemma mul_comm (a b : mynat) : a * b = b * a :=
begin [nat_num_game]
    induction b with d hd,
    {
        rw mul_zero,
        rw zero_mul,
        refl,
    },
    {
        rw mul_succ,
        rw succ_mul,
        rw hd,
        refl,
    },
end

end mynat