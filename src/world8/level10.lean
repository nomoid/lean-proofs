import mynat.definition
import mynat.add
import world8.level6
import world8.level9

namespace mynat

theorem add_left_eq_zero (a b : mynat) (h : a + b = 0) : b = 0 :=
begin [nat_num_game]
    cases b with d,
    {
        refl,
    },
    {
        exfalso,
        rw add_succ at h,
        apply succ_ne_zero (a + d),
        exact h,
    },
end

end mynat
