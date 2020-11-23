import mynat.definition
import mynat.mul
import world3.level5
import world3.level8

namespace mynat

lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin [nat_num_game]
    induction b with d hd,
    {
        rw mul_comm 0,
        rw mul_comm 0,
        repeat {rw mul_zero},
    },
    {
        rw ← mul_assoc,
        rw ← mul_assoc,
        rw mul_comm a,
        refl,
    },
end

end mynat