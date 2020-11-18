import mynat.definition
import mynat.add

namespace mynat

lemma add_succ_zero (a : mynat) : a + succ(0) = succ(a) :=
begin [nat_num_game]
    rw add_succ,
    rw add_zero,
    refl
end

end mynat