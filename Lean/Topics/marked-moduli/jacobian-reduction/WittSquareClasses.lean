import WittBasis

/-! A common unramified quadratic extension for all even-order differences.
The base residue field can already be an extension of the prime field. -/
open Polynomial IsDiscreteValuationRing
namespace ZInQBlueprint.WittSquareClasses
noncomputable section
variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [CharP k p]
abbrev Extension := FiniteField.Extension k p 2
local notation "R" => WittVector p k
local notation "E" => Extension p k
local notation "W" => WittVector p E

instance extensionChar : CharP (Extension p k) p :=
  charP_of_injective_algebraMap' k p

def extend : R →+* W := WittVector.map (algebraMap k E)
instance extensionAlgebra : Algebra R W := (extend p k).toAlgebra

theorem square_in_residue (b : k) : ∃ r : E, r^2 = algebraMap k E b := by
  have split := ResidueExtension.splits_of_small_degree p k 2 2
    (by intro j hj hj'; interval_cases j <;> decide) (X^2 - C b) (by compute_degree)
  obtain ⟨r, hr⟩ := split.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by
    rw [natDegree_map, natDegree_X_pow_sub_C]; decide))
  exact ⟨r, by simpa [sub_eq_zero] using hr⟩

def residueIso : IsLocalRing.ResidueField W ≃+* E :=
  (Ideal.quotEquivOfEq (WittVector.irreducible p (k := E)).maximalIdeal_eq).trans
    WittVector.quotientPEquiv

theorem unit_sqrt (hp : 2 < p) (u : Rˣ) : ∃ y : W, y^2 = extend p k (u : R) := by
  let ρ := IsLocalRing.residue W
  let e := residueIso p k
  let b := WittVector.constantCoeff (p := p) (u : R)
  obtain ⟨r, hr⟩ := square_in_residue p k b
  have he : e (ρ (extend p k (u : R))) = algebraMap k E b := rfl
  let r' := e.symm r
  have hr' : r'^2 = ρ (extend p k (u : R)) := e.injective (by simpa [r'] using hr.trans he.symm)
  have hunit := (u.isUnit.map (extend p k)).map ρ
  have hr0 : r' ≠ 0 := by
    intro z
    exact hunit.ne_zero (by rw [← hr', z, zero_pow (by decide)])
  have htwo : (2 : E) ≠ 0 := by
    change ((2 : ℕ) : E) ≠ 0
    rw [Ne, CharP.cast_eq_zero_iff E p]
    exact Nat.not_dvd_of_pos_of_lt (by decide) hp
  have h2 : (2 : IsLocalRing.ResidueField W) ≠ 0 := fun h =>
    htwo (by simpa only [map_ofNat, map_zero] using congrArg e h)
  let f : W[X] := X^2 - C (extend p k (u : R))
  let : HenselianRing W (IsLocalRing.maximalIdeal W) := by
    rw [(WittVector.irreducible p (k := E)).maximalIdeal_eq]
    infer_instance
  obtain ⟨y, hy, _⟩ := HenselTriples.liftSimple f r'
    (by simpa [f, ρ, sub_eq_zero] using hr')
    (by
      rw [show f.derivative = C (2 : W) * X by simp [f, derivative_sub, derivative_pow]]
      rw [eval₂_mul, eval₂_C, eval₂_X, map_ofNat]
      exact mul_ne_zero h2 hr0)
  exact ⟨y, by simpa [Polynomial.IsRoot, f, sub_eq_zero] using hy⟩

/-- A single ring contains square roots of every nonzero integral element of even order. -/
theorem even_sqrt (hp : 2 < p) {x : R} {n : ℕ}
    (hx : addVal R x = ((2*n : ℕ) : ℕ∞)) : ∃ y : W, y^2 = extend p k x := by
  have hne : x ≠ 0 := by
    rintro rfl
    exact ENat.natCast_ne_top (2*n) (hx.symm.trans (AddValuation.map_zero _))
  have hπ : Irreducible (p : R) := WittVector.irreducible p
  obtain ⟨m, u, h⟩ := eq_unit_mul_pow_irreducible hne hπ
  have hm := ENat.natCast_inj.mp ((addVal_def x u hπ m h).symm.trans hx)
  obtain ⟨y, hy⟩ := unit_sqrt p k hp u
  refine ⟨y * (p : W)^n, ?_⟩
  rw [h, map_mul, map_pow, map_natCast, mul_pow, hy, ← pow_mul, hm, Nat.mul_comm n 2]

/-- The quantifiers put all square roots in the same extension, even for an
infinite index set. This applies to all ordered differences of the five roots. -/
theorem simultaneous {ι : Type*} (hp : 2 < p) (x : ι → R)
    (h : ∀ i, ∃ n : ℕ, addVal R (x i) = ((2*n : ℕ) : ℕ∞)) :
    ∃ y : ι → W, ∀ i, y i ^ 2 = extend p k (x i) := by
  exact Classical.axiomOfChoice (fun i => (h i).elim (fun _ e => even_sqrt p k hp e))

end
end ZInQBlueprint.WittSquareClasses
#print axioms ZInQBlueprint.WittSquareClasses.square_in_residue
#print axioms ZInQBlueprint.WittSquareClasses.unit_sqrt
#print axioms ZInQBlueprint.WittSquareClasses.even_sqrt
#print axioms ZInQBlueprint.WittSquareClasses.simultaneous
