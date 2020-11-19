import mynat.definition
import mynat.add
import world2.level4
import world8.level5

namespace mynat

theorem add_left_cancel (a t b : mynat) : t + a = t + b → a = b :=
begin [nat_num_game]
    rw add_comm t a,
    rw add_comm t b,
    exact add_right_cancel a t b,
end

end mynat