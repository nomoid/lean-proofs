import mynat.definition
import mynat.add
import world8.level4
import world8.level5

namespace mynat

theorem add_right_cancel_iff (a t b : mynat) : a + t = b + t ↔ a = b :=
begin [nat_num_game]
    split,
    {
        exact add_right_cancel a t b,
    },
    {
        induction t with n hd,
        {
            rw add_zero,
            rw add_zero,
            intro h,
            exact h,
        },
        {
            intro h,
            have res := hd h,
            rw add_succ,
            rw add_succ,
            rw eq_iff_succ_eq_succ,
            exact res,
        },
    },
end

end mynat