import mynat.definition
import mynat.add
import mynat.mul

namespace mynat

example : mynat → mynat :=
begin
    intro n,
    exact 3*n + 2,
end

end mynat