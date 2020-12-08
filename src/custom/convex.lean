import analysis.normed_space.basic

universe u

variables {E : Type u} [add_comm_group E] [vector_space ℝ E]

-- Definition of convex modified from Lean library analysis.convex

def contains_entire_segment (s: set E) (x y : E) :=
    ∀ (a b : ℝ),
    0 ≤ a →
    0 ≤ b →
    a + b = 1 →
    a • x + b • y ∈ s

def convex (s : set E) :=
    ∀ (x y : E),
    x ∈ s →
    y ∈ s →
    contains_entire_segment s x y

-- Lemma: Given sets s1 and s2 and x where x ∈ x1 ∩ s2,
--        x ∈ s1.
lemma intersection_left (s1 s2: set E) (x : E) : x ∈ s1 ∩ s2 → x ∈ s1 :=
begin
    intro h,
    cases h with hleft hright,
    exact hleft
end

-- Lemma: Given sets s1 and s2 and x where x ∈ x1 ∩ s2,
--        x ∈ s2.
lemma intersection_right (s1 s2: set E) (x : E) : x ∈ s1 ∩ s2 → x ∈ s2 :=
begin
    intro h,
    cases h with hleft hright,
    exact hright
end

-- Lemma: Given sets s1 and s2 and points x and y where
--        s1 contains the entire segment between x and y and
--        s2 contains the entire segment between x and y,
--        s1 ∩ s2 contains the entire segment between x and y.
lemma intersection_contains_entire_segment (s1 s2 : set E) (x y : E) :
    contains_entire_segment s1 x y ∧ contains_entire_segment s2 x y →
    contains_entire_segment (s1 ∩ s2) x y :=
begin
    intros h a b nna nnb ab1,
    cases h with h1 h2,
    split,
    {
        exact h1 a b nna nnb ab1,
    },
    {
        exact h2 a b nna nnb ab1,
    }
end

-- Theorem: Given sets s1 and s2 where s1 and s2 are convex,
--          s1 ∩ s2 is convex.
theorem intersection_convex (s1 s2 : set E) :
    convex s1 → convex s2 → convex (s1 ∩ s2) :=
begin
    -- Given convex sets s1 and s2,
    intros hs1 hs2,
    -- Given points p1 and p2 in s1 ∩ s2,
    intros p1 p2 p1inter p2inter,
    -- We want to show that every point on the path between p1 and p2 are
    -- in s1 ∩ s2.
    apply intersection_contains_entire_segment,
    split,
    -- First we show that every point on the path is in s1.
    {
        -- Since p1 is in s1 ∩ s2, p1 is in s1.
        have p1s1 := intersection_left s1 s2 p1 p1inter,
        -- Since p2 is in s1 ∩ s2, p2 is in s1.
        have p2s1 := intersection_left s1 s2 p2 p2inter,
        -- By the definition of convex, since s1 is convex,
        apply hs1,
        -- And p1 and p2 are in s1,
        exact p1s1,
        exact p2s1,
        -- We have that every point on the path between p1 and p2 are in s1.
    },
    {
        -- Since p1 is in s1 ∩ s2, p1 is in s2.
        have p1s2 := intersection_right s1 s2 p1 p1inter,
        -- Since p2 is in s1 ∩ s2, p2 is in s2.
        have p2s2 := intersection_right s1 s2 p2 p2inter,
        -- By the definition of convex, since s2 is convex,
        apply hs2,
        -- And p1 and p2 are in s2,
        exact p1s2,
        exact p2s2,
        -- We have that every point on the path between p1 and p2 are in s2.
    },
end