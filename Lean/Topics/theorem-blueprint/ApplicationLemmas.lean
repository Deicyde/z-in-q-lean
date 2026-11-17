import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Local deductions in the six-contact and congruent-number arguments. -/
namespace ZInQBlueprint

/-- TYZ write `d y² = x³ − x`. The construction uses `Y² = X³ − d² X`. -/
theorem twist_change (d x y : ℚ) (hd : d ≠ 0) :
    d * y^2 = x^3 - x ↔ (d^2*y)^2 = (d*x)^3 - d^2*(d*x) := by
  constructor
  · intro h
    linear_combination d^3 * h
  · intro h
    apply (mul_left_cancel₀ (pow_ne_zero 3 hd) :
      d^3 * (d*y^2) = d^3 * (x^3-x) → _)
    linear_combination h

/-- The inverse affine map recovers the same rational point. -/
theorem twist_change_inverse (d X Y : ℚ) (hd : d ≠ 0) :
    d * (X/d) = X ∧ d^2 * (Y/d^2) = Y := by
  constructor <;> field_simp

/-- Multiplying the abscissa by `d` changes its prescribed squareclass by `d`. -/
theorem twist_squareclass (d x a : ℚ) :
    IsSquare ((d*x)/a) ↔ IsSquare (x/(a/d)) := by
  rw [div_div_eq_mul_div]; ring_nf

/-- The four units of ℤ[i], given by their real and imaginary parts. -/
theorem norm_one_coordinates (r s : ℤ) (h : r^2+s^2=1) :
    (r=1 ∧ s=0) ∨ (r= -1 ∧ s=0) ∨ (r=0 ∧ s=1) ∨ (r=0 ∧ s= -1) := by
  have bound (x y : ℤ) (he : x^2+y^2=1) : -1 ≤ x ∧ x ≤ 1 := by
    constructor
    · by_contra! hneg
      have hpos : 0 < (x+1)*(x+1) := mul_pos_of_neg_of_neg (by omega) (by omega)
      nlinarith [sq_nonneg y]
    · by_contra! hpos
      have : 0 < (x-1)*(x-1) := mul_pos (by omega) (by omega)
      nlinarith [sq_nonneg y]
  obtain ⟨_,_⟩ := bound r s h
  obtain ⟨_,_⟩ := bound s r (by linarith)
  have hr : r= -1 ∨ r=0 ∨ r=1 := by omega
  have hs : s= -1 ∨ s=0 ∨ s=1 := by omega
  rcases hr with h|h|h <;> rcases hs with k|k|k <;> subst r <;> subst s <;> norm_num at *

/-- Twice the period relation at the end of the proof of TYZ 3.5(2).
The two coefficients are both even for every Gaussian unit and every lattice lift. -/
theorem gaussian_period_parity (a b : ℤ) (u z : Zsqrtd (-1))
    (unitNorm : u.re^2+u.im^2=1)
    (period : (a : Zsqrtd (-1))*u*⟨1,-1⟩+(b : Zsqrtd (-1))=2*z) :
    2 ∣ a ∧ 2 ∣ b := by
  have hre := congrArg Zsqrtd.re period
  have him := congrArg Zsqrtd.im period
  simp at hre him
  rcases norm_one_coordinates _ _ unitNorm with ⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩ <;>
    simp [h,k] at hre him <;> omega

/-- If the first factor has class seven and the residual product has class one,
the second distinguished factor in the genus sum has class three. -/
theorem complementary_factor_mod_eight (n a b t : ℕ) (fact : n=a*b*t)
    (hn : n%8=5) (ha : a%8=7) (ht : t%8=1) : b%8=3 := by
  rw [fact, Nat.mul_mod, ht, Nat.mul_mod a b, ha] at hn
  omega

/-- Eight distinct realized classes exhaust an eight-element descent set.
The application must construct the injection into the actual Selmer classes. -/
theorem all_classes_of_eight {α : Type*} {S : Set α} (hS : S.ncard=8)
    (realized : α → Prop) (f : Fin 8 → α) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ S) (hreal : ∀ i, realized (f i)) :
    ∀ a ∈ S, realized a := by
  have sub : Set.range f ⊆ S := Set.range_subset_iff.mpr hmem
  have card : (Set.range f).ncard=8 := by simp [Set.ncard_range_of_injective hf]
  have eqn := Set.eq_of_subset_of_ncard_le sub (by omega) (Set.finite_of_ncard_pos (by omega))
  intro a ha
  rw [←eqn] at ha
  obtain ⟨i,rfl⟩ := ha
  exact hreal i

/-- Compose the two numerical height estimates at the *same* surface.
The values H and M in the application are max(1,C_cm,Q_R^17) and M_S(u). -/
theorem six_contact_comparison {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (hu hf H M : F) (coordinate : hu ≤ 10^13 * max 1 hf)
    (surface : max 1 hf ≤ H * M^24) : hu ≤ (2*10^13*H)*M^24 := by
  have h := le_trans coordinate (mul_le_mul_of_nonneg_left surface (by positivity : (0:F) ≤ 10^13))
  have hpos : 0 ≤ H*M^24 := le_trans (le_trans zero_le_one (le_max_left _ _)) surface
  calc hu ≤ 10^13*(H*M^24) := h
       _ ≤ (2*10^13)*(H*M^24) := mul_le_mul_of_nonneg_right (by norm_num) hpos
       _ = _ := by ring

#print axioms twist_change
#print axioms twist_change_inverse
#print axioms twist_squareclass
#print axioms gaussian_period_parity
#print axioms complementary_factor_mod_eight
#print axioms all_classes_of_eight
#print axioms six_contact_comparison
end ZInQBlueprint
