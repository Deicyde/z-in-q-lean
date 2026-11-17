import ScalarSignChoice

namespace Sun28.MultiplierChoice
open Sun28.Ordinary Sun28.WitnessIndices Sun28.Concrete Sun28.TraceAtlas Sun28.Forward
  Sun28.ScalarHeight Sun28.FixedPreparation ZInQ
noncomputable section

/-- Reflection keeps the actual two free pole parameters e,z. -/
theorem neg_pole_at (B e z:ℚ) : poleAt smallMultipliers (-B) e z ↔ poleAt smallMultipliers B e z := by
  have turn (q:ℚ) : poleAt smallMultipliers q e z → poleAt smallMultipliers (-q) e z := by
    rintro (zero|⟨m,mem,h⟩)
    · exact Or.inl (by rw [zero,neg_zero])
    · exact Or.inr ⟨-m,neg_listed mem,(neg_branch m q e z).mpr h⟩
  exact ⟨fun h => by simpa only [neg_neg] using turn (-B) h,turn B⟩

theorem sign_tests_iff (w:NinePoints) (p:Fin 28→ℚ) (s:Bool) :
    signTests w p s ↔ signTests w p true := by
  cases s
  · unfold signTests
    have flip (r W:ℚ) : signedValue r (sign false) gamma denominator W =
        -signedValue r (sign true) gamma denominator W := by simp [sign,signedValue]
    simp_rw [flip,neg_pole_at]
  · rfl

/-- Omit the entire scalar-negative ordinate list before elimination. -/
def oneSignBranches : List (Sun28.Compiler.Branch 28) := ordinatePanels (branchProgram true)

theorem accepted_one_sign (p : Fin 28 → ℚ) : Accepted oneSignBranches p ↔ Accepted fixedBranches p := by
  have spec (s:Bool) := ordinate_panels_spec (p:=p) (branchProgram s)
    (S:=fun a => sideData (nineAffine a).doubles ∧ signTests (nineAffine a).doubles p s)
    (impl:=fun a _ v t h => program_spec p t v a s h)
  rw [oneSignBranches, fixedBranches, accepted_flat, spec]
  constructor
  · intro h; exact ⟨true,by simp,(spec true).mpr h⟩
  · rintro ⟨s,_,h⟩
    obtain ⟨a,hp,side,t⟩ := (spec s).mp h
    exact ⟨a,hp,side,(sign_tests_iff _ _ s).mp t⟩

def oneSignPolynomial : MvPolynomial (Fin 29) ℤ :=
  Sun28.Branches.polynomial28 (Sun28.Compiler.branchAtlas oneSignBranches)

private theorem compile_spec (rows : List (Sun28.Compiler.Branch 28)) (x:ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28
      (Sun28.Branches.polynomial28 (Sun28.Compiler.branchAtlas rows)) x w=0) ↔
    ∃ z : Fin 27 → ℚ, Accepted rows (Fin.cases x z) := by
  rw [Sun28.Branches.polynomial28_spec]
  simp_rw [Sun28.Compiler.branchAtlas_spec]
  rfl

/-- Literal projected zero loci agree at every rational input. -/
theorem compiled_one_sign (x:ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 oneSignPolynomial x w=0) ↔
    ∃ w : Fin 28 → ℚ, Sun28.eval28 fixedPolynomial x w=0 := by
  have branch : (∃ z : Fin 27 → ℚ, Accepted oneSignBranches (Fin.cases x z)) ↔
      ∃ z : Fin 27 → ℚ, Accepted fixedBranches (Fin.cases x z) := by
    constructor
    · rintro ⟨z,h⟩; exact ⟨z,(accepted_one_sign _).mp h⟩
    · rintro ⟨z,h⟩; exact ⟨z,(accepted_one_sign _).mpr h⟩
  unfold oneSignPolynomial fixedPolynomial
  exact Iff.trans (compile_spec oneSignBranches x) (Iff.trans branch (compile_spec fixedBranches x).symm)
end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.neg_pole_at
#print axioms Sun28.MultiplierChoice.sign_tests_iff
#print axioms Sun28.MultiplierChoice.accepted_one_sign
#print axioms Sun28.MultiplierChoice.compiled_one_sign
