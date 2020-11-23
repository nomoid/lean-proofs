import mynat.definition
import mynat.mul
import world3.level4

namespace mynat

lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin [nat_num_game]
    induction c with d hd,
    {
        repeat {rw mul_zero},
    },
    {
        rw mul_succ,
        rw mul_succ,
        rw mul_add,
        rw ← hd,
        refl,
    },
end

end mynat