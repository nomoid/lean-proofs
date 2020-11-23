import mynat.definition
import mynat.mul
import world2.level2
import world2.level5
import world2.level6

namespace mynat

lemma succ_mul (a b : mynat) : succ(a) * b = a * b + b :=
begin [nat_num_game]
    induction b with d hd,
    {
        repeat {rw mul_zero},
        rw add_zero,
        refl,
    },
    {
        rw mul_succ,
        rw hd,
        rw mul_succ,
        rw succ_eq_add_one,
        rw succ_eq_add_one,
        rw ← add_assoc,
        rw ← add_assoc,
        rw add_right_comm (a * d),
        refl,
    },
end

end mynat