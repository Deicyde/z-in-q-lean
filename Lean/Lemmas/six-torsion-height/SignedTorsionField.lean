import LocalTorsionDescent
import MonicRootChart
import SixFixedPoints
import RationalJacobian
import ChartBaseChange
import Mathlib.NumberTheory.NumberField.Basic

/-! One finite number field for the full level and the ramification points of
the actual signed six-contact curve, with the restricted monic equation. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.TorsionHeight
open BinaryCover SixJacobian WeightedCurvePoints
noncomputable section
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

def OddPointChart (f : Polynomial ℚ) (K : Type) [Field K] [NumberField K] : Prop :=
  let p := f.map (algebraMap ℚ K)
  ∃ a : K, p.IsRoot a ∧ p.derivative.eval a ≠ 0 ∧
    (oddPolynomial p a).Monic ∧ (oddPolynomial p a).natDegree = 5 ∧
    Nonempty ({v : K × K // v.2 ^ 2 = p.eval v.1 ∧ v.1 ≠ a} ≃
      {v : K × K // v.2 ^ 2 = (oddPolynomial p a).eval v.1 ∧ v.1 ≠ 0})

include hu in
theorem six_sections_when_split {K : Type} [Field K] [CharZero K]
    (h : (paper K u false).Splits) :
    Nat.card (fixedSections K u) = 6 ∧ Nonempty (fixedSections K u) := by
  classical
  let f := paper K u false
  have hd := finite_degree K hu
  have hf : f ≠ 0 := by intro H; change f.natDegree = 6 at hd; simp [H] at hd
  let e : {x : K // f.IsRoot x} ≃ (↑f.roots.toFinset : Type) :=
    Equiv.subtypeEquivProp (by funext x; simp [Polynomial.mem_roots hf])
  have count : Nat.card (fixedSections K u) = 6 := by
    rw [←Nat.card_congr (Equiv.ofBijective _ (rootSection_bijective K hu)), Nat.card_congr e]
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots (paper_chart_regular K hu false).2), ←h.natDegree_eq_card_roots,hd]
  obtain ⟨a,ha⟩ := h.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by rw [hd]; decide))
  exact ⟨count,⟨rootSection K u ⟨a,ha⟩⟩⟩

/-- There are six distinct rational ramification sections and a monic quintic
chart over a single field carrying all 12-division points of the rational group. -/
theorem signed_height_field :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      FullLevel (SixJacobian.jacobian hu) 12 K ∧
      (paper K u false).Splits ∧ Nat.card (fixedSections K u) = 6 ∧
      Nonempty (fixedSections K u) ∧ OddPointChart (paper ℚ u false) K := by
  let A := SixJacobian.jacobian hu
  let : IsProper A.X.hom := (SixJacobian.isAbelian hu).proper
  let : Smooth A.X.hom := (SixJacobian.isAbelian hu).smooth
  let f := paper ℚ u false
  have hd : f.natDegree = 6 := finite_degree ℚ hu
  have hf : f ≠ 0 := by intro H; simp [H] at hd
  obtain ⟨K,kf,ka,kdim,sp,level⟩ := exists_full_level ℚ A (12:ℕ+) (by norm_num) f hf
  let := kf
  let := ka
  let := kdim
  let nk : NumberField K := NumberField.of_module_finite ℚ K
  have eqA : ka = (DivisionRing.toRatAlgebra : Algebra ℚ K) := Subsingleton.elim _ _
  rw [eqA] at sp level
  have hk : (paper K u false).Splits := by rw [←paper_baseChange]; exact sp
  obtain ⟨six,pt⟩ := six_sections_when_split hu hk
  refine ⟨K,kf,nk,level,hk,six,pt,?_⟩
  unfold OddPointChart
  rw [paper_baseChange]
  have degree := finite_degree K hu
  obtain ⟨a,ha⟩ := hk.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by rw [degree]; decide))
  have hs : (paper K u false).derivative.eval a ≠ 0 := by
    simpa only [eval₂_id] using (paper_chart_regular K hu false).2.eval₂_derivative_ne_zero
      (RingHom.id K) (by simpa only [eval₂_id] using ha)
  obtain ⟨monic,deg⟩ := oddPolynomial_monic_degree (paper K u false) a
  exact ⟨a,ha,hs,monic,deg,⟨oddOpenEquiv (le_of_eq degree) ha hs⟩⟩

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.six_sections_when_split
#print axioms ZInQBlueprint.TorsionHeight.signed_height_field
