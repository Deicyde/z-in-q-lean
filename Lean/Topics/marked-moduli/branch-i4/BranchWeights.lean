import SexticThetaHeight
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Reconstruction of a sextic from six distinct roots in the given order. -/
namespace ZInQBlueprint.BranchI4
open Polynomial
noncomputable section

/-- The left side has no normalization of its leading coefficient. -/
theorem factorization (f : ℚ[X]) (hd : f.natDegree = 6) (r : Fin 6 → ℂ)
    (hr : Function.Injective r) (hroot : ∀ i, aeval (r i) f = 0) :
    f.map (algebraMap ℚ ℂ) = C (f.leadingCoeff : ℂ) * ∏ i, (X - C (r i)) := by
  classical
  let g := f.map (algebraMap ℚ ℂ)
  let e : Fin 6 ↪ ℂ := ⟨r, hr⟩
  let S := Finset.univ.map e
  have hc : S.card = 6 := by simp [S]
  have hdg : g.natDegree = 6 := (natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective f).trans hd
  have hg : g ≠ 0 := by intro h; simp [h] at hdg
  have hR : g.roots = S.val := roots_eq_of_natDegree_le_card_of_ne_zero (fun x hx => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact (eval_map_algebraMap f _).trans (hroot i)) (hdg.trans hc.symm).le hg
  have he := (C_leadingCoeff_mul_prod_multiset_X_sub_C (p := g)
    (hR ▸ hc.trans hdg.symm)).symm
  rw [hR] at he
  have hLC : g.leadingCoeff = (f.leadingCoeff : ℂ) := leadingCoeff_map_of_injective (algebraMap ℚ ℂ).injective f
  rw [hLC] at he
  change g = C (f.leadingCoeff : ℂ) * ∏ x ∈ Finset.univ, (X-C (r x))
  convert he using 2
  change (∏ i, (X-C (r i))) = ∏ x ∈ S, (X-C x)
  rw [Finset.prod_map]
  rfl

/-- The ascending Vandermonde factors on a triple. -/
def triple (r : Fin 6 → ℂ) (i j k : Fin 6) : ℂ :=
  (r i-r j)*(r i-r k)*(r j-r k)

def weight (r : Fin 6 → ℂ) (i j a b c : Fin 6) : ℂ :=
  (triple r i j 5 * triple r a b c)^2

def weightSum (r : Fin 6 → ℂ) : ℂ :=
  weight r 0 1 2 3 4 + weight r 0 2 1 3 4 + weight r 0 3 1 2 4 +
  weight r 0 4 1 2 3 + weight r 1 2 0 3 4 + weight r 1 3 0 2 4 +
  weight r 1 4 0 2 3 + weight r 2 3 0 1 4 + weight r 2 4 0 1 3 +
  weight r 3 4 0 1 2

end
end ZInQBlueprint.BranchI4
#print axioms ZInQBlueprint.BranchI4.factorization
