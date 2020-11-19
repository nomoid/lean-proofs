import mynat.definition
import mynat.add
import world8.level4

namespace mynat

theorem ne_succ_self (n : mynat) : n ≠ succ(n) :=
begin [nat_num_game]
    induction n with d hd,
    {
        exact zero_ne_succ 0,
    },
    {
        intro h,
        apply hd,
        apply succ_inj,
        exact h,
    },
end

-- theorem ne_succ_self (n : mynat) : n ≠ succ(n) :=
-- begin [nat_num_game]
--     induction n with d hd,
--     {
--         exact zero_ne_succ 0,
--     },
--     {
--         rw ne_from_not_eq at hd,
--         rw ← eq_iff_succ_eq_succ at hd,
--         rw ← ne_from_not_eq at hd,
--         exact hd,
--     },
-- end

end mynat
