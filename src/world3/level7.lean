import mynat.definition
import mynat.mul
import world2.level2
import world2.level5
import world2.level6

namespace mynat

lemma add_mul (a b c : mynat) : (a + b) * c = a * c + b * c :=
begin [nat_num_game]
    induction c with d hd,
    {
        repeat {rw mul_zero},
        rw add_zero,
        refl,
    },
    {
        rw mul_succ,
        rw hd,
        rw mul_succ,
        rw mul_succ,
        rw ← add_assoc,
        rw ← add_assoc,
        rw add_right_comm (a * d),
        refl,
    },
end

end mynat