import mynat.definition
import mynat.add
import world8.level6
import world8.level9

namespace mynat

theorem add_right_eq_zero (a b : mynat) (h : a + b = 0) : a = 0 :=
begin [nat_num_game]
    cases a with d,
    {
        refl,
    },
    {
        exfalso,
        rw succ_add at h,
        apply succ_ne_zero (d + b),
        exact h,
    },
end

end mynat
