import mynat.definition
import mynat.add
import world2.level1
import world2.level3

namespace mynat

lemma add_comm (a b : mynat) : a + b = b + a :=
begin [nat_num_game]
    induction b with d hd,
    {
        rw zero_add,
        refl,
    },
    {
        rw add_succ,
        rw succ_add,
        rw hd,
        refl,
    }
end

end mynat
