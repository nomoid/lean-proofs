import mynat.definition
import mynat.add
-- import world2.level1
-- import world2.level3
-- import world6.level8
-- import world7.level1
-- import world8.level4
import world8.level6

namespace mynat

theorem eq_zero_of_add_right_eq_self (a b : mynat) : a + b = a → b = 0 :=
begin [nat_num_game]
    intro h,
    apply add_left_cancel b a,
    rw add_zero,
    exact h,
end

-- lemma add_succ_ne_self (a b : mynat) : a + succ(b) ≠ a :=
-- begin [nat_num_game]
--     induction a with n hd,
--     {
--         rw zero_add,
--         rw ne_comm,
--         exact zero_ne_succ b,
--     },
--     {
--         rw succ_add,
--         rw ne_from_not_eq,
--         rw eq_iff_succ_eq_succ,
--         rw ← ne_from_not_eq,
--         exact hd,
--     },
-- end

-- theorem eq_zero_of_add_right_eq_self (a b : mynat) : a + b = a → b = 0 :=
-- begin [nat_num_game]
--     induction b with n hd,
--     {
--         intro h,
--         refl,
--     },
--     {
--         intro h,
--         exfalso,
--         have nh := add_succ_ne_self a n,
--         rw ne_from_not_eq at nh,
--         rw not_iff_imp_false at nh,
--         have f := nh h,
--         exact f,
--     },
-- end

end mynat