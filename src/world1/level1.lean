import mynat.definition
import mynat.add
import mynat.mul

namespace mynat

lemma example1 (x y z : mynat) : x * y + z = x * y + z :=
begin [nat_num_game]
    refl
end

end mynat