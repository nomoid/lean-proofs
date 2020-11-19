import mynat.definition
import mynat.add

namespace mynat

theorem succ_ne_zero (a : mynat) : succ(a) ≠ 0 :=
begin [nat_num_game]
    symmetry,
    exact zero_ne_succ a,
end

end mynat
