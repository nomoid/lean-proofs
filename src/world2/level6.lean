import mynat.definition
import mynat.add
import world2.level2
import world2.level4

namespace mynat

lemma add_right_comm (a b c: mynat) : a + b + c = a + c + b :=
begin [nat_num_game]
    rw add_assoc,
    rw add_comm b,
    rw add_assoc,
    refl,
end

end mynat
