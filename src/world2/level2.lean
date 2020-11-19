import mynat.definition
import mynat.add
import world2.level1

namespace mynat

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin [nat_num_game]
    induction c with d hd,
    {
        rw add_zero,
        rw add_zero,
        refl,
    },
    {
        rw add_succ,
        rw add_succ,
        rw add_succ,
        rw hd,
        refl,
    }
end

end mynat