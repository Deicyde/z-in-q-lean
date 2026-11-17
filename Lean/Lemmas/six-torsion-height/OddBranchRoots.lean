import MonicRootChart
import Mathlib.FieldTheory.Separable

/-! Distinct branch points of the odd monic equation. -/
open Polynomial
namespace ZInQBlueprint.TorsionHeight
noncomputable section
variable {K : Type*} [Field K] {f : K[X]} {a : K}

theorem odd_zero (hd : f.natDegree = 6) :
    (oddPolynomial f a).eval 0 = f.derivative.eval a ^ 4 * f.leadingCoeff := by
  simp [oddPolynomial, ←hd, coeff_taylor_natDegree]

/-- Inverting about a simple root sends the other five roots bijectively to
the roots of the transformed quintic. -/
theorem odd_roots_split_separable (hd : f.natDegree = 6) (split : f.Splits)
    (sep : f.Separable) (ha : f.IsRoot a) :
    (oddPolynomial f a).Splits ∧ (oddPolynomial f a).Separable ∧
      (oddPolynomial f a).eval 0 ≠ 0 := by
  classical
  let q := oddPolynomial f a
  let c := f.derivative.eval a
  have hc : c ≠ 0 := by
    simpa only [c,eval₂_id] using sep.eval₂_derivative_ne_zero (RingHom.id K)
      (by simpa only [eval₂_id] using ha.eq_zero)
  have hn : f ≠ 0 := fun h => by simp [h] at hd
  have hq : q.natDegree = 5 := (oddPolynomial_monic_degree f a).2
  have hqn : q ≠ 0 := fun h => by simp [h] at hq
  let others := f.roots.toFinset.erase a
  let z (x : K) := c / (x-a)
  have count : others.card = 5 := by
    have ha' : a ∈ f.roots.toFinset := by simpa [mem_roots hn] using ha
    rw [Finset.card_erase_of_mem ha', Multiset.toFinset_card_of_nodup (nodup_roots sep),
      ←split.natDegree_eq_card_roots, hd]
  have inj : Function.Injective z := by
    intro x y eq
    change c / (x-a) = c / (y-a) at eq
    have hi : (x-a)⁻¹ = (y-a)⁻¹ := mul_left_cancel₀ hc (by simpa only [div_eq_mul_inv] using eq)
    exact sub_left_inj.mp (inv_injective hi)
  have sub : others.image z ⊆ q.roots.toFinset := by
    rintro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨ne,hx⟩ := Finset.mem_erase.mp hx
    have root : f.IsRoot x := (mem_roots hn).mp (Multiset.mem_toFinset.mp hx)
    have sum := odd_evaluation hd.le ha ne
    rw [root.eq_zero,mul_zero] at sum
    exact Multiset.mem_toFinset.mpr ((mem_roots hqn).mpr <|
      (mul_eq_zero.mp sum).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr ne)))
  have card' := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj, count] at card'
  have hle := Multiset.toFinset_card_le q.roots
  have hund := card_roots' q
  have hsplit : q.Splits := splits_iff_card_roots.mpr (by omega)
  refine ⟨hsplit, (nodup_roots_iff_of_splits hqn hsplit).mp
    (Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)), ?_⟩
  rw [odd_zero hd]
  exact mul_ne_zero (pow_ne_zero 4 hc) (leadingCoeff_ne_zero.mpr hn)

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.odd_zero
#print axioms ZInQBlueprint.TorsionHeight.odd_roots_split_separable

