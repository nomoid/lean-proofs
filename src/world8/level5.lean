import mynat.definition
import mynat.add

namespace mynat

theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b :=
begin [nat_num_game]
    induction t with n hd,
    {
        rw add_zero,
        rw add_zero,
        intro h,
        exact h,
    },
    {
        rw add_succ,
        rw add_succ,
        intro h,
        apply hd,
        apply succ_inj,
        exact h,
    },
end

end mynat