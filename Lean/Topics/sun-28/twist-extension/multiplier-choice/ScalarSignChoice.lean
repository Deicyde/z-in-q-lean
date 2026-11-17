import FixedCertificate

namespace Sun28.MultiplierChoice
open Sun28.Ordinary Sun28.ScalarHeight Sun28.Scalar Sun28.Forward Sun28.WitnessIndices
  Sun28.FixedPreparation Sun28.Concrete ZInQ
noncomputable section

theorem neg_listed {μ:ℚ} (member:μ∈smallMultipliers) : -μ∈smallMultipliers := by
  obtain ⟨⟨g,a,b,i⟩,_,rfl⟩:=Finset.mem_image.mp member
  refine Finset.mem_image.mpr ⟨(!g,a,b,i),Finset.mem_univ _,?_⟩
  cases g <;> cases a <;> cases b <;> simp [shift]

theorem neg_branch (μ B e z:ℚ) : poleBranch (-μ) (-B) e z ↔ poleBranch μ B e z := by
  simp [poleBranch]

theorem neg_pole (B:ℚ) : polePredicate smallMultipliers (-B) ↔ polePredicate smallMultipliers B := by
  have flip (q:ℚ) : polePredicate smallMultipliers q → polePredicate smallMultipliers (-q) := by
    rintro (rfl|⟨m,mem,e,z,h⟩)
    · exact Or.inl neg_zero
    · exact Or.inr ⟨-m,neg_listed mem,e,z,(neg_branch m q e z).mpr h⟩
  exact ⟨fun h=>by simpa using flip (-B) h,flip B⟩

private theorem signed_negative (r g W:ℚ) (d:ℕ) :
    signedValue r (-1) g d W = -signedValue r 1 g d W := by
  simp [signedValue]

/-- The full scalar test on the actual six coefficients, with the sign fixed. -/
theorem scalar_sign (w:NinePoints) (M:ℕ) (r g:ℚ) (d:ℕ) :
    scalarAccepted w M r g d smallMultipliers ↔
      let W:=scalarTree r (scalarEntries w M)
      W≠0 ∧ polePredicate smallMultipliers (signedValue r 1 g d W) := by
  constructor
  · rintro ⟨δ,sgn,wn,h⟩
    refine ⟨wn,?_⟩
    rcases sgn with rfl|rfl
    · exact h
    · rw [signed_negative] at h
      exact (neg_pole _).mp h
  · rintro ⟨wn,h⟩;exact ⟨1,Or.inl rfl,wn,h⟩

/-- An exact presentation of the zero set of the fixed polynomial. Only one
scalar sign, at its original tree and original nine input doubles, is required. -/
theorem polynomial_one_sign (x:ℚ) :
    (∃w:Fin 28→ℚ,Sun28.eval28 fixedPolynomial x w=0) ↔
    ∃ (a:Fin 9→AffineInput) (η:ℚ),
      let w:=(nineAffine a).doubles
      let r:=scalarRadicand (beta x)
      let W:=scalarTree r (scalarEntries w fixedMultiplier)
      Guards w anchor ∧
      (∀ j,(pointScale w fixedMultiplier j)^2*η∉marks ∧
        (pointScale w fixedMultiplier j)^2*η≠3 ∧ pointScale w fixedMultiplier j≠0) ∧
      (∀ j,let s:=pointScale w fixedMultiplier j
        ordinaryAccepted w fixedMultiplier anchor (beta x) (s^2) (s^2*η) smallMultipliers) ∧
      W≠0 ∧ polePredicate smallMultipliers (signedValue r 1 gamma denominator W) := by
  rw [polynomial_iff_certificate]
  constructor
  · rintro ⟨a,η,h⟩
    refine ⟨a,η,⟨h.q_nonzero,h.h_nonzero,h.base_nonzero,(rational_chart_iff _).mp h.odd_N,
      (rational_chart_iff _).mp h.odd_T,(rational_chart_iff _).mp h.odd_Z⟩,
      h.scale_guard,h.ordinary,?_⟩
    exact (scalar_sign ..).mp h.scalar
  · rintro ⟨a,η,⟨qn,hn,bn,n,t,z⟩,scales,o,wn,sc⟩
    exact ⟨a,η,qn,hn,bn,(rational_chart_iff _).mpr n,(rational_chart_iff _).mpr t,
      (rational_chart_iff _).mpr z,scales,o,(scalar_sign ..).mpr ⟨wn,sc⟩⟩
end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.neg_listed
#print axioms Sun28.MultiplierChoice.neg_branch
#print axioms Sun28.MultiplierChoice.neg_pole
#print axioms Sun28.MultiplierChoice.scalar_sign
#print axioms Sun28.MultiplierChoice.polynomial_one_sign
