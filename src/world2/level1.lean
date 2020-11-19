import mynat.definition
import mynat.add

namespace mynat

lemma zero_add (n : mynat) : 0 + n = n :=
begin [nat_num_game]
    induction n with d hd,
    {
        rw add_zero,
        refl,
    },
    {
        rw add_succ,
        rw hd,
        refl,
    },
end

end mynat