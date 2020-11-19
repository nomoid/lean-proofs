lemma maze (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=
begin
    have q := h(p),
    have t := j(q),
    have u := l(t),
    exact u,
end