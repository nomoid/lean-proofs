import mynat.definition
import mynat.mul
import world2.level1

namespace mynat

lemma mul_one (m : mynat) : m * 1 = m :=
begin [nat_num_game]
    rw one_eq_succ_zero,
    rw mul_succ,
    rw mul_zero,
    rw zero_add,
    refl,
end

end mynat