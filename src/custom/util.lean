import logic.basic
import algebra.order
import data.nat.basic

lemma ne_self_imp_false : ∀ (a : ℕ), a ≠ a → false :=
begin
    intro a,
    intro h,
    rw ne.def at h,
    rw ne_self_iff_false at h,
    exact h,
end

lemma gt_zero_of_ne_zero : ∀ (a : ℕ), a ≠ 0 → 0 < a :=
begin
    intro a,
    intro h,
    induction a with d hd,
    {
        exfalso,
        apply ne.irrefl,
        exact h,
    },
    {
        apply lt_of_le_not_le,
        {
            apply nat.le.intro,
            apply zero_add,
        },
        {
            intro h2,
            have h3 := nat.le.dest h2,
            cases h3 with n hn,
            have h4 := nat.eq_zero_of_add_eq_zero hn,
            have h5 := h4.left,
            have h6 := nat.succ_ne_zero d,
            rw ← h5 at h6,
            apply ne_self_imp_false,
            exact h6,
        },
    },
end

lemma ne_zero_iff_gt_zero : ∀ (a : ℕ), a ≠ 0 ↔ 0 < a :=
begin
    intro a,
    split,
    {
        apply gt_zero_of_ne_zero,
    },
    {
        intro h,
        apply ne_of_gt,
        exact h,
    },
end

lemma mul_left_cancel_0 (a b c : ℕ) (h: c ≠ 0) : a * c = b * c → a = b :=
begin
    have hc := gt_zero_of_ne_zero c h,
    intro h2,
    by_contradiction hab,
    rw ← ne.def at hab,
    rw ne_iff_lt_or_gt at hab,
    cases hab,
    repeat {
        have h3 := mul_lt_mul_of_pos_right hab hc,
        have h4 := ne_of_lt h3,
        rw h2 at h4,
        apply ne_self_imp_false,
        exact h4,
    },
end

lemma ge_zero (n : ℕ) : 0 ≤ n :=
begin
    apply @nat.le.intro 0 n n,
    rw zero_add,
end

lemma one_or_two (n : ℕ) (h: 0 < n ∧ n ≤ 2) : n = 1 ∨ n = 2 :=
begin
    have h2 := @classical.or_not (n ≥ 2),
    cases h2,
    {
        right,
        apply eq_iff_le_not_lt.2,
        split,
        {
            exact and.right h,
        },
        {
            apply not_lt_of_ge,
            exact h2,
        },
    },
    {
        left,
        apply eq_iff_le_not_lt.2,
        split,
        {
            apply nat.le_of_lt_succ,
            apply lt_of_not_ge,
            exact h2,
        },
        {
            apply not_lt_of_ge,
            apply nat.le_of_lt_succ,
            apply nat.succ_lt_succ,
            exact and.left h,
        },
    },
end

lemma zero_or_one (a : ℕ) : a = 0 ∨ a = 1 ↔ a < 2 :=
begin
    split,
    {
        intro h,
        cases h,
        {
            rw h,
            apply nat.lt_of_succ_le,
            apply le_of_lt,
            apply nat.lt_of_succ_le,
            refl,
        },
        {
            rw h,
            apply nat.lt_of_succ_le,
            refl,
        },
    },
    {
        intro h,
        cases (@classical.or_not (a ≥ 1)) with h2 h2n,
        {
            right,
            apply eq_iff_le_not_lt.2,
            split,
            {
                apply nat.le_of_lt_succ,
                exact h,
            },
            {
                apply not_lt_of_ge,
                exact h2
            },
        },
        {
            left,
            apply eq_iff_le_not_lt.2,
            split,
            {
                apply nat.le_of_lt_succ,
                apply lt_of_not_ge,
                exact h2n,
            },
            {
                apply not_lt_of_ge,
                apply ge_zero,
            },
        },
    },
end

lemma gt_zero_of_eq_one (n : ℕ) : n = 1 → 0 < n :=
begin
    intro h,
    rw h,
    apply lt_add_one,
end