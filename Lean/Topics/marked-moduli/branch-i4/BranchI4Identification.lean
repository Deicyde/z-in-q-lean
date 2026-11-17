import BranchI4Sum

/-! The sum of the ten unordered triple-pair weights is the fourth invariant
of the monic polynomial. The fourth power of the leading coefficient restores
the normalization of the rational sextic. -/
namespace ZInQBlueprint.BranchI4
open Polynomial SexticInvariants SexticThetaHeight
noncomputable section

theorem rational_i4_sum (f : ℚ[X]) (hd : f.natDegree = 6) (r : Fin 6 → ℂ)
    (hr : Function.Injective r) (hh : ∀ i, aeval (r i) f = 0) :
    (f.leadingCoeff : ℂ)^4 * weightSum r = (igusaI4 f : ℂ) := by
  let a := rootsCoeff r
  have hc (k : Fin 7) := factor_coeff f hd r hr hh k
  have h := scale_quartic (f.leadingCoeff : ℂ) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)
  rw [monic_i4_sum,quartic_eq]
  change _ = quartic (f.coeff ((0 : Fin 7):ℕ)) (f.coeff ((1 : Fin 7):ℕ))
    (f.coeff ((2 : Fin 7):ℕ)) (f.coeff ((3 : Fin 7):ℕ)) (f.coeff ((4 : Fin 7):ℕ))
    (f.coeff ((5 : Fin 7):ℕ)) (f.coeff ((6 : Fin 7):ℕ))
  rw [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]
  exact h.symm

theorem sextic_i4_sum {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    (r : Fin 6 → ℂ) (hr : Function.Injective r) (hh : ∀ i, aeval (r i) (sextic u δ) = 0) :
    ((sextic u δ).leadingCoeff : ℂ)^4 * weightSum r = (igusaI4 (sextic u δ) : ℂ) :=
  rational_i4_sum _ (smooth_sextic hu hδ).1 r hr hh

end
end ZInQBlueprint.BranchI4
#print axioms ZInQBlueprint.BranchI4.rational_i4_sum
#print axioms ZInQBlueprint.BranchI4.sextic_i4_sum
