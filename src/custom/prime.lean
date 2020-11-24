import data.nat.prime
import polyfill.factorial
import polyfill.mod
import logic.basic
import custom.util

namespace nat

lemma dvd_gt_zero (n m : ℕ) (h : 0 < m) : n ∣ m → 0 < n :=
begin
    intro h2,
    rw dvd_iff_mod_eq_zero at h2,
    by_contra h3,
    rw ← ne_zero_iff_gt_zero at h3,
    rw ne.def at h3,
    rw not_not at h3,
    rw h3 at h2,
    have h3 := mod_zero m,
    rw h3 at h2,
    rw ← ne_zero_iff_gt_zero at h,
    rw h2 at h,
    apply ne_self_imp_false,
    exact h,
end

lemma two_is_prime : prime 2 :=
begin
    split,
    {
        apply le_of_eq,
        refl,
    },
    {
        intro m,
        intro h,
        apply one_or_two,
        split,
        {
            apply dvd_gt_zero m 2,
            apply zero_lt_one_add,
            exact h,
        },
        {
            apply le_of_dvd,
            apply zero_lt_one_add,
            exact h,
        },
    }
end

lemma ge_two_of_factor_not_one (a b : ℕ) (h : a ≠ 1) (h2 : 2 ≤ b) : b % a = 0 → 2 ≤ a :=
begin
    intro hd,
    apply le_of_not_gt,
    rw gt_from_lt,
    rw ← zero_or_one,
    apply not_or,
    {
        by_contra haz,
        have hmz := mod_zero b,
        rw haz at hd,
        rw hmz at hd,
        have hzo := @or.inl (b = 0) (b = 1) hd,
        rw zero_or_one at hzo,
        have h2n := not_le_of_gt hzo,
        apply absurd h2 h2n,
    },
    {
        rw ← ne.def,
        exact h,
    },
end

lemma exists_prime_factor : ∀ (n : ℕ), 2 ≤ n → ∃ (p : ℕ), prime p ∧ n % p = 0 :=
begin
    intro n,
    intro h,
    have hnge2 := le.dest h,
    cases hnge2 with m hm,
    rw ← hm,
    clear hm,
    induction m using nat.case_strong_induction_on with d hd,
    {
        use 2,
        split,
        {
            exact two_is_prime,
        },
        {
            rw add_zero,
            exact mod_self 2,
        }
    },
    {
        have h2 := @classical.or_not (prime (2 + succ d)),
        cases h2,
        {
            use (2 + succ d),
            split,
            {
                exact h2,
            },
            {
                apply mod_self,
            }
        },
        {
            rw prime_def_lt at h2,
            rw not_and at h2,
            have h2lsd := @le_add_right 2 (succ d),
            have h3 := h2 h2lsd,
            have hnf1 := classical.not_forall.1,
            have h4 := hnf1 h3,
            cases h4 with x hx,
            have h5 := not_imp.1 hx,
            have h6 := not_imp.1 (h5.right),
            have hxne1 := h6.right,
            rw ← ne.def at hxne1,
            have hxdvd := h6.left,
            have hmodx := mod_eq_zero_of_dvd hxdvd,
            have hxge2 := ge_two_of_factor_not_one x (2 + succ d) hxne1 h2lsd hmodx,
            cases (le.dest hxge2) with y hy,
            have hlt := h5.left,
            rw ← hy at hlt,
            have hyltsd := lt_of_add_lt_add_left hlt,
            have hyled := le_of_lt_succ hyltsd,
            have hdy := hd y hyled,
            cases hdy with p hp,
            use p,
            split,
            {
                apply hp.left,
            },
            {
                apply mod_eq_zero_of_dvd,
                apply dvd_trans,
                {
                    rw dvd_iff_mod_eq_zero,
                    apply hp.right,
                },
                {
                    rw hy,
                    exact hxdvd,
                },
            },
        },
    },
end

lemma factorial_mod_zero (n d : ℕ) (h : d ≤ n) (h2 : 1 ≤ d) : (factorial n) % d = 0 :=
begin
    apply mod_eq_zero_of_dvd,
    apply dvd_factorial,
    {
        exact h2,
    },
    {
        exact h,
    },
end

lemma mod_zero_add_one_is_one (n d : ℕ) (h: 2 ≤ d) : n % d = 0 → (n + 1) % d = 1 :=
begin
    intro hmz,
    rw add_comm,
    rw ← @add_mod_mod 1 n d,
    rw hmz,
    rw add_zero,
    have hle := le.dest h,
    cases hle with c hc,
    rw ← hc,
    rw add_comm,
    apply one_mod,
end

theorem infinite_primes (n : ℕ) (h : 2 ≤ n) : ∃ (p : ℕ), prime p ∧ p > n :=
begin
    have hfng2 := le_trans h (self_le_factorial n),
    have hfnp1g2 := le_trans hfng2 (le_add_right (factorial n) 1),
    have h1 := exists_prime_factor (factorial n + 1) hfnp1g2,
    cases h1 with p hp,
    use p,
    split,
    {
        exact hp.left,
    },
    {
        have hprime := hp.left,
        by_contra hnpgn,
        apply absurd hp.right,
        rw ← ne_from_not_eq ((factorial n + 1) % p) 0,
        apply ne_of_gt,
        apply gt_zero_of_eq_one,
        apply mod_zero_add_one_is_one,
        {
            apply prime.two_le,
            apply hprime,
        },
        {
            rw ← dvd_iff_mod_eq_zero,
            apply dvd_factorial,
            {
                apply lt_of_succ_le,
                apply le_of_succ_le,
                apply prime.two_le,
                apply hprime,
            },
            {
                apply le_of_not_gt,
                exact hnpgn,
            },
        },
    },
end

end nat