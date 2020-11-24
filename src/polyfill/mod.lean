/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/

/- excerpt of https://github.com/leanprover-community/mathlib/blob/fee93e961d7b74a4b0ce9e454b8a960e48acc3b2/src/data/nat/basic.lean -/
namespace nat

@[simp] lemma one_mod (n : ℕ) : 1 % (n + 2) = 1 := nat.mod_eq_of_lt (add_lt_add_right n.succ_pos 1)

@[simp] theorem mod_add_mod (m n k : ℕ) : (m % n + k) % n = (m + k) % n :=
by have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm;
   rwa [add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : ℕ) : (m + n % k) % k = (m + n) % k :=
by rw [add_comm, mod_add_mod, add_comm]

end nat
