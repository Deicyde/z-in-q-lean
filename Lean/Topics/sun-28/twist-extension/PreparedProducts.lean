import LocalProducts

namespace Sun28.TwistExtension
open PreparedPoles PairedClasses TwistRank TwistPrimes
noncomputable section

/-- Above each eligible β, fix one nontrivial factor and vary the second one
without bound. Every output satisfies all fixed-place and admissibility tests. -/
theorem unbounded_products {β : ℕ} (bp : 0<β) (bs : Squarefree β) (b6 : β.Coprime 6)
    (bm : β%24=17) : ∃ d : ℕ, 1<d ∧ ∀ B : ℕ, ∃ e : ℕ, B<d*e ∧ 1<e ∧
    d.Coprime e ∧ AdmissiblePair β (d*e) ∧ FixedSquares (d*e) ∧
    Family β d ∧ Family β e ∧ FactorPair β (d*e) ∧ Surface (β:ℚ) ((d*e:ℕ):ℚ) ∧ ¬(β*d).Coprime (d*e) := by
  obtain ⟨d,large,ad,fd,f,_⟩:=fixed_factor bp bs b6 bm (by decide : 0<1) (Nat.coprime_one_right _) 1
  refine ⟨d,large,?_⟩
  intro B
  obtain ⟨e,he,ae,fe,g,cd⟩:=fixed_factor bp bs b6 bm ad.2.1 ad.2.2.2.2.1 (max B 1)
  have cap : e≤d*e:=by simpa only [one_mul] using Nat.mul_le_mul_right e large.le
  have pair : FactorPair β (d*e):=⟨d,e,ad.2.1,ae.2.1,rfl,Or.inl f,Or.inl g⟩
  exact ⟨e,((le_max_left ..).trans_lt he).trans_le cap,(le_max_right ..).trans_lt he,cd.symm,
    admissible_mul ad ae cd.symm,fixed_mul fd fe,f,g,pair,surface_of_factors bp (Nat.mul_pos ad.2.1 ae.2.1) pair,
    shared_divisor large⟩

end
end Sun28.TwistExtension
#print axioms Sun28.TwistExtension.unbounded_products
