import data.nat.prime
import polyfill.factorial
import polyfill.mod
import logic.basic
import custom.util

/- 
    The following code contains a theorem that proves that
    there are infinitely many prime numbers. Specifically,
    the statement of the theorem is that:

    If `n` is a natural number, there exists some prime
    number `p` that is greater than `n`.

    Given that `2` is prime, we can iteratively apply the
    above theorem to show that there are infinitely many
    primes.

    The proof of infinitely many primes will be explained
    in detail. However, before the theorem statement, there
    are also several lemmas presented here that are used in
    the proof of the theorem, in addition to those that are
    imported from the Lean standard library `mathlib`.
-/

namespace nat

/- Lemma: Given naturals `n` and `m` where `n` divides `m`
   and `m > 0`, we have that `n > 0`. -/
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

/- Lemma: `2` is a prime number, where prime is defined as
   being `≥ 2` and having exactly `1` and itself as
   factors. -/
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

/- Lemma: Given a factor of a natural number `≥ 2`, if that
   factor is not `1`, it must be also `≥ 2` -/
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

/- Lemma: Given a natural number `≥ 2`, that number has at
   least one factor that is prime. -/
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

/- Lemma: Given a natural number `n`, every natural number
   between `1` and `n` inclusive divides `n` factorial. -/
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

/- Lemma: Given `d ≥ 2` and `n`, where `n mod d` is `0`,
   `n + 1 mod d` is `1`. -/
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

/-
    Theorem: Given a natural number `n ≥ 2`, there exists a
    prime `p` where `p > n`.

    This proof is inspired by Euclid's proof of existence
    of infinitely many primes. The proof will be written
    inline accompanying the corresponding Lean code.
-/   
-- Let `n` be a natural number such that `n ≥ 2`.
theorem infinite_primes (n : ℕ) (h : 2 ≤ n) : ∃ (p : ℕ), prime p ∧ p > n :=
begin
    -- We have that `n! ≥ n` as a property of factorials.
    have hnlnf := self_le_factorial n,
    -- Since `n ≥ 2`, it must be the case that `n! ≥ 2`.
    have hfng2 := le_trans h hnlnf,
    -- Thus, `n! + 1 ≥ 2`.
    have hfnp1g2 := le_trans hfng2 (le_add_right (factorial n) 1),
    -- From an above lemma, we have shown that any `x ≥ 2`
    -- has a prime factor.
    -- Therefore, `n! + 1` has a prime factor.
    have h1 := exists_prime_factor (factorial n + 1) hfnp1g2,
    -- Let `p` be a prime factor of `n! + 1`.
    cases h1 with p hp,
    -- We want to show that `p` is a prime greater than `n`.
    use p,
    -- `p` is prime because it is a prime factor of
    -- `n! + 1`.
    have hprime := hp.left,
    split,
    -- We will start by showing that `p` is prime.
    {
        -- We have already shown just now that `p` is
        -- prime, so we are done.
        exact hprime,
    },
    -- Now we have to show that `p > n`.
    {
        -- By contradiction, assume that it is not the case
        -- that `p > n`.
        by_contra hnpgn,
        -- At this point, we will work backwards to show
        -- that a contradiction occurs. This backwards
        -- solving style may be a bit unituitive for
        -- reading a regular proof in, but it is the style
        -- that is preferred by Lean.
        -- Since we have shown that `n! + 1` has `p` as a
        -- factor, we can create a contradiction by showing
        -- that `n! + 1` does not have `p` has a factor.
        apply absurd hp.right,
        -- To do this, we want to show that
        -- `(n! + 1) mod p ≠ 0`.
        rw ← ne_from_not_eq ((factorial n + 1) % p) 0,
        -- This can be achieved by showing that
        -- `(n! + 1) mod p > 0`.
        apply ne_of_gt,
        -- This can be achieved by showing that
        -- `(n! + 1) mod p = 1`.
        apply gt_zero_of_eq_one,
        -- If we know that `n! mod p = 0`, along with
        -- `p ≥ 2`, we can use one
        -- of our above lemmas to show that
        -- `(n! + 1) mod p = 1`.
        apply mod_zero_add_one_is_one,
        -- First we need to show that `p ≥ 2`.
        {
            -- We know that all primes `p` satisfy `p ≥ 2`,
            -- so we just need to show that `p` is prime.
            apply prime.two_le,
            -- However, we have already shown that `p` is
            -- prime, so we can conclude `p ≥ 2`.
            apply hprime,
        },
        -- Now we need to show that `n! mod p = 0`.
        {
            -- We can rewrite this as `p divides n!`.
            rw ← dvd_iff_mod_eq_zero,
            -- We can use the basic property of factorials
            -- where for all `0 < p ≤ n`, `p divides n!`.
            apply dvd_factorial,
            -- First we need to show that `p > 0`.
            {
                -- This is equivalent to `p ≥ 1`.
                apply lt_of_succ_le,
                -- We know that `p ≥ 1` when `p ≥ 2`.
                apply le_of_succ_le,
                -- Which is true if `p` is a prime.
                apply prime.two_le,
                -- And we already know that `p` is a prime,
                -- so we can conclude that `p > 0`.
                apply hprime,
            },
            -- Lastly, we need to show that `p ≤ n`.
            {
                -- This is equivalent to showing the
                -- inverse of `p > n`.
                apply le_of_not_gt,
                -- We assumed in our contradiction that it
                -- is not the case that `p > n`. Thus,
                -- `p ≤ n`.
                exact hnpgn,
            },
            -- We are now done with the proof!
            -- As a recap of the backwards logic,
            -- by contradiction, we assumed that `p ≤ n`.
            -- Therefore, since `p ≥ 0`, we have that
            -- `p divides n!`.
        },
        -- Therefore, `n! mod p = 0`.
        -- Therefore, since `p ≥ 2`, `(n! + 1) mod p = 1`.
        -- However, we defined `p` as being a prime factor
        -- of `(n! + 1)`, so `(n! + 1) mod p = 0`.
        -- This is a contradiction, so it must be the case
        -- that `p > n`.
        -- Since we have already shown that `p` is prime,
        -- we can conclude that for all natural numbers
        -- `n`, there exists a prime `p` such that `p > n`.
    },
end

end nat