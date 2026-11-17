import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The quadratic chart s² = −6j over the generic vertical prime. -/
namespace ZInQBlueprint.QuadraticChart
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R]

/-- The equation defining the chart in the Baba–Granath parameter. -/
def equation (j : R) : R[X] := X^2 + C (6*j)

abbrev Chart (j : R) := AdjoinRoot (equation j)

def root (j : R) : Chart j := AdjoinRoot.root (equation j)

theorem equation_monic (j : R) : (equation j).Monic :=
  monic_X_pow_add_C _ (by decide)

theorem root_sq (j : R) : (root j)^2 = -algebraMap R (Chart j) (6*j) := by
  have h : aeval (root j) (equation j) = 0 := by
    rw [root, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [eq_neg_iff_add_eq_zero]
  simpa only [equation, map_add, map_pow, aeval_X, aeval_C] using h

theorem derivative_at_root (j : R) :
    AdjoinRoot.mk (equation j) (equation j).derivative = 2 * root j := by
  have hd : (equation j).derivative = 2 * X := by
    simp [equation, derivative_add]
    ring
  rw [hd, map_mul, map_ofNat, AdjoinRoot.mk_X]
  rfl

theorem derivative_unit (j : R) (h2 : IsUnit (2:R)) (h6j : IsUnit (6*j)) :
    IsUnit (AdjoinRoot.mk (equation j) (equation j).derivative) := by
  have hs2 : IsUnit ((root j)^2) := by rw [root_sq]; exact (h6j.map _).neg
  have hs := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hs2
  rw [derivative_at_root]
  exact (show IsUnit (2:Chart j) by simpa only [map_ofNat] using h2.map (algebraMap R (Chart j))).mul hs

/-- The monic quadratic algebra itself is finite étale, before any localization of this algebra. -/
theorem finite_etale (j : R) (h2 : IsUnit (2:R)) (h6j : IsUnit (6*j)) :
    Module.Finite R (Chart j) ∧ Algebra.Etale R (Chart j) := by
  refine ⟨(equation_monic j).finite_adjoinRoot, ?_⟩
  let P : StandardEtalePair R :=
    ⟨equation j, equation_monic j, (equation j).derivative, 1, 0, 1, by simp⟩
  have hu : IsUnit (AdjoinRoot.mk P.f P.g) := derivative_unit j h2 h6j
  let e := (IsLocalization.atUnit (AdjoinRoot P.f)
    (Localization.Away (AdjoinRoot.mk P.f P.g)) _ hu).restrictScalars R
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans e.symm)

/-- The quadratic quotient has a basis of length two over any nontrivial base. -/
theorem basis_two (j : R) [Nontrivial R] : Nonempty (Module.Basis (Fin 2) R (Chart j)) := by
  have hd : (equation j).natDegree = 2 := natDegree_X_pow_add_C
  exact ⟨(AdjoinRoot.powerBasisAux' (equation_monic j)).reindex (finCongr hd)⟩

/-- The same criterion in a base ring in which 2, 3 and j are visibly units. -/
theorem finite_etale_of_units (j : R) (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hj : IsUnit j) :
    Module.Finite R (Chart j) ∧ Algebra.Etale R (Chart j) := by
  apply finite_etale j h2
  have h6 : IsUnit (6:R) := by convert h2.mul h3 using 1; norm_num
  exact h6.mul hj

/-- The vertical prime of the integral j-line cut out by coefficientwise reduction modulo p. -/
def verticalIdeal (p : ℕ) : Ideal ℤ[X] :=
  RingHom.ker (mapRingHom (Int.castRingHom (ZMod p)))

/-- This kernel is the principal vertical prime (p) in the integral parameter line. -/
theorem verticalIdeal_eq_span (p : ℕ) :
    verticalIdeal p = Ideal.span ({C (p : ℤ)} : Set ℤ[X]) := by
  ext f
  rw [Ideal.mem_span_singleton, C_dvd_iff_dvd_coeff]
  change (f.map (Int.castRingHom (ZMod p)) = 0) ↔ _
  constructor
  · intro h n
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa using congrArg (fun g : (ZMod p)[X] => g.coeff n) h
  · intro h
    ext n
    rw [coeff_map, coeff_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h n)

instance verticalIdeal_prime (p : ℕ) [Fact p.Prime] : (verticalIdeal p).IsPrime :=
  RingHom.ker_isPrime _

abbrev VerticalRing (p : ℕ) [Fact p.Prime] := Localization.AtPrime (verticalIdeal p)

def verticalParameter (p : ℕ) [Fact p.Prime] : VerticalRing p :=
  algebraMap ℤ[X] (VerticalRing p) X

private theorem vertical_isUnit {p : ℕ} [Fact p.Prime] (f : ℤ[X])
    (hf : f.map (Int.castRingHom (ZMod p)) ≠ 0) :
    IsUnit (algebraMap ℤ[X] (VerticalRing p) f) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (VerticalRing p) (verticalIdeal p) f).mpr
  exact hf

private theorem small_constant_unit {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (hlt : n < p) :
    IsUnit (n : VerticalRing p) := by
  have hn' : (n : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hn hlt
  have hC : (C (n : ZMod p)) ≠ 0 := (map_ne_zero_iff C C_injective).mpr hn'
  have hc := vertical_isUnit (p:=p) (C (n:ℤ)) (by simpa using hC)
  simpa using hc

/-- At the vertical prime the parameter is a unit even though it is transcendental in the residue field. -/
theorem vertical_units (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    IsUnit (2 : VerticalRing p) ∧ IsUnit (3 : VerticalRing p) ∧ IsUnit (verticalParameter p) := by
  refine ⟨small_constant_unit (n:=2) (by decide) (by omega), small_constant_unit (n:=3) (by decide) (by omega), ?_⟩
  exact vertical_isUnit X (by simp)

theorem vertical_finite_etale (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Module.Finite (VerticalRing p) (Chart (verticalParameter p)) ∧
      Algebra.Etale (VerticalRing p) (Chart (verticalParameter p)) := by
  obtain ⟨h2,h3,hj⟩ := vertical_units p hp
  exact finite_etale_of_units _ h2 h3 hj

#print axioms root_sq
#print axioms derivative_at_root
#print axioms derivative_unit
#print axioms basis_two
#print axioms finite_etale
#print axioms finite_etale_of_units
#print axioms verticalIdeal_eq_span
#print axioms vertical_units
#print axioms vertical_finite_etale
end
end ZInQBlueprint.QuadraticChart
