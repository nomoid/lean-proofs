import mynat.definition
import mynat.add
import world2.level1
import world2.level3

namespace mynat

lemma succ_eq_add_one (a : mynat) : succ(a) = a + 1 :=
begin [nat_num_game]
    induction a with d hd,
    {
        rw zero_add,
        rw one_eq_succ_zero,
        refl,
    },
    {
        rw succ_add,
        rw hd,
        refl,
    }
end

end mynat
