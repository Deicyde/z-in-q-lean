import MarkedPartner

namespace Sun28.SeededPartners
open Sun28.SelmerRealization Sun28.PairedClasses Sun28.PreparedPoles ZInQ.RouteK.Selmer

/-- Local membership for a marked twist from two sets of residue tests. -/
theorem marked_local {b c : ℕ} (sb : Squarefree b) (b8 : b%8=1)
    (c3 : c%3=1) (cop : b.Coprime c)
    (at_b : ∀ p, p.Prime → p∣b → IsSquare (c:ZMod p))
    (at_c : ∀ p, p.Prime → p∣c → IsSquare (b:ZMod p)) :
    ((b:ℤ),1) ∈ localClasses (b*c) := by
  refine ⟨Int.squarefree_natCast.mpr sb,squarefree_one,
    square_chart (Or.inl (Real.isSquare_iff.mpr (by positivity))),fun p _ => ?_⟩
  have pp : p.Prime := Fact.out
  by_cases two : p=2
  · subst p
    have m : (b:ℤ) ≡ 1 [ZMOD 8] := by change (b:ℤ)%8=1%8;omega
    have H := isSquare_intCast_div_two_adic (m:=(b:ℤ)) (n:=1) (by decide) m
    exact square_chart (Or.inl (by simpa using H))
  by_cases three : p=3
  · subst p
    have mod3 : (c:ZMod 3)=1 := (ZMod.natCast_eq_natCast_iff' c 1 3).mpr c3
    apply square_chart (Or.inr (lift_unit two (by omega) ?_))
    rw [mod3]
    exact IsSquare.one
  by_cases pb : p∣b
  · exact square_chart (Or.inr (lift_unit two (fun pc=>pp.not_dvd_one (cop ▸ Nat.dvd_gcd pb pc)) (at_b p pp pb)))
  by_cases pc : p∣c
  · exact square_chart (Or.inl (lift_unit two pb (at_c p pp pc)))
  have big := pp.two_le
  exact good_place (by omega) pb pc

/-- The mutual-square conditions on the prescribed second input preserve
local solubility of the marked class on the companion twist. -/
theorem partner_local {b d q : ℕ} (ad : AdmissiblePair b d) (cop : b.Coprime q)
    (q3 : q%3=1)
    (at_b : ∀ p, p.Prime → p∣b → IsSquare (q:ZMod p))
    (at_q : ∀ p, p.Prime → p∣q → IsSquare (b:ZMod p)) :
    ((b:ℤ),1) ∈ localClasses ((b*q)*d) := by
  obtain ⟨_,_,sb,_,bd,_,_,bm,dm,b_at_d,d_at_b⟩ := ad
  rw [Nat.mul_assoc]
  apply marked_local sb (by omega) (by rw [Nat.mul_mod,q3,show d%3=1 by omega])
    (cop.mul_right bd)
  · intro p pp pb
    let _ : Fact p.Prime := ⟨pp⟩
    rw [Nat.cast_mul]
    exact (at_b p pp pb).mul (residue_of_local_square (d_at_b p pp pb))
  · intro p pp pc
    let _ : Fact p.Prime := ⟨pp⟩
    rcases pp.dvd_mul.mp pc with pq|pd
    · exact at_q p pp pq
    · exact residue_of_local_square (b_at_d p pp pd)

end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.marked_local
#print axioms Sun28.SeededPartners.partner_local
