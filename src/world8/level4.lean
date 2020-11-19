import mynat.definition
import world8.level3

namespace mynat

theorem eq_iff_succ_eq_succ (a b : mynat) : succ(a) = succ(b) ↔ a = b :=
begin
    split,
    {
        exact succ_inj,
    },
    {
        exact succ_eq_succ_of_eq,
    },
end

end mynat