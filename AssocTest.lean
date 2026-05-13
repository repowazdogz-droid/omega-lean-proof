def test (a b c d : Prop) (h : a ∧ b ∧ c ∧ d) : d := h.2.2.2
def test2 (a b c d : Prop) (h : a ∧ b ∧ c ∧ d) : d := h.2.2.2.1
