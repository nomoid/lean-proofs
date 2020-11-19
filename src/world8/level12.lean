import mynat.definition
import mynat.add
import world2.level5

namespace mynat

theorem add_one_eq_succ (d : mynat) : d + 1 = succ(d) :=
begin [nat_num_game]
    symmetry,
    exact succ_eq_add_one d,
end

end mynat
