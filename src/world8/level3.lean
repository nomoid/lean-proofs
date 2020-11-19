import mynat.definition

namespace mynat

theorem succ_eq_succ_of_eq {a b : mynat} : a = b → succ(a) = succ(b) :=
begin
    intro a,
    rw a,
end

end mynat