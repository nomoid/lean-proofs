import mynat.definition

namespace mynat

lemma example3 (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b) :=
begin [nat_num_game]
    rw h,
    refl
end

end mynat