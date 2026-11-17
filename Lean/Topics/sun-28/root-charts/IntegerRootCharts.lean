import OrdinateCharts

/-! Sun, §8.1. A signed square root over ℚ(√2) from one root of an integer-monic equation. -/
open Polynomial
namespace Sun28.RootCharts
open Ordinates
noncomputable section
variable {R : Type*} [CommRing R]

/-- Polynomial in one new variable. A, B and D belong to the earlier coefficient ring. -/
def polynomial (k : Branch) (A B D : R) : R[X] :=
  match k with
  | .mixed => X^4 - C (4*D*A)*X^2 + C (8*D^2*B^2)
  | .realPart => X^2 - C (4*D*A)
  | .radicalPart => X^2 - C (2*D*A)
  | .zero => X

theorem polynomial_monic (k : Branch) (A B D : R) : (polynomial k A B D).Monic := by
  cases k with
  | mixed =>
    suffices ∀ p q : R, (X^4-C p*X^2+C q).Monic by apply this
    intro p q
    nontriviality R
    monicity <;> decide
  | realPart | radicalPart => exact monic_X_pow_sub_C _ (by decide)
  | zero => exact monic_X

/-- Evaluated root equation after specializing the previously chosen variables. -/
def value (k : Branch) (a b d w : ℚ) : ℚ :=
  match k with
  | .mixed => w^4 - 4*d*a*w^2 + 8*d^2*b^2
  | .realPart => w^2 - 4*d*a
  | .radicalPart => w^2 - 2*d*a
  | .zero => w

theorem specialized_root (φ : R →+* ℚ) (k : Branch) (A B D : R) (w : ℚ) :
    ((polynomial k A B D).map φ).IsRoot w ↔ value k (φ A) (φ B) (φ D) w = 0 := by
  cases k <;> norm_num [polynomial,value,IsRoot.def,map_ofNat]

/-- The mixed chart records the denominator of the reconstructed second coordinate. -/
def guard (k : Branch) (a b d w : ℚ) : Prop := d ≠ 0 ∧ match k with
  | .mixed => b ≠ 0 ∧ w ≠ 0
  | .realPart | .radicalPart => b = 0 ∧ a ≠ 0
  | .zero => a = 0 ∧ b = 0

/-- The full sign of the point is recovered from the root w. -/
def reconstruct (k : Branch) (b d w : ℚ) : K :=
  match k with
  | .mixed => pair (w/(2*d)) (b/w)
  | .realPart => pair (w/(2*d)) 0
  | .radicalPart => pair 0 (w/(2*d))
  | .zero => 0

theorem reconstruct_scaled (k : Branch) (b d t : ℚ) (hd : d ≠ 0) :
    reconstruct k b d (2*d*t) = k.point (b/d) t := by
  have ht : 2*d*t/(2*d)=t := by field_simp
  have hb : b / (2*d*t) = b/d/(2*t) := by rw [div_div]; ring_nf
  cases k <;> simp [reconstruct,Branch.point,ht,hb]

theorem condition_scaled (k : Branch) (a b d t : ℚ) (hd : d ≠ 0) :
    k.condition (a/d) (b/d) t ↔
        guard k a b d (2*d*t) ∧ value k a b d (2*d*t) = 0 := by
  have hdz : 2*d ≠ 0 := mul_ne_zero (by norm_num) hd
  have hdz' : 2*d^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hd)
  have hA : a/d=0 ↔ a=0 := by simp [hd]
  have hB : b/d=0 ↔ b=0 := by simp [hd]
  cases k with
  | mixed =>
    have hV : value .mixed a b d (2*d*t) = (2*d)^4 * quartic (a/d) (b/d) t := by
      unfold value quartic; field_simp; ring
    have hv : value .mixed a b d (2*d*t)=0 ↔ quartic (a/d) (b/d) t=0 := by
      rw [hV]
      simp [hd]
    change (b/d ≠ 0 ∧ quartic (a/d) (b/d) t=0) ↔
      (d ≠ 0 ∧ b ≠ 0 ∧ 2*d*t ≠ 0) ∧ _
    rw [hv]
    constructor
    · rintro ⟨hb,hq⟩
      have ht : t ≠ 0 := by
        rintro rfl
        exact hb (by simpa [quartic] using hq)
      exact ⟨⟨hd,fun h => hb (hB.mpr h),mul_ne_zero hdz ht⟩,hq⟩
    · rintro ⟨⟨_,hb,_⟩,hq⟩
      exact ⟨fun h => hb (hB.mp h),hq⟩
  | realPart =>
    have hV : value .realPart a b d (2*d*t) = (2*d)^2*(t^2-a/d) := by
      unfold value; field_simp; ring
    simp [guard,Branch.condition,hA,hB,hd,hV,sub_eq_zero,and_assoc]
  | radicalPart =>
    have hV : value .radicalPart a b d (2*d*t) = 2*d^2*(2*t^2-a/d) := by
      unfold value; field_simp
    simp [guard,Branch.condition,hA,hB,hd,hV,hdz',sub_eq_zero,and_assoc]
  | zero => simp [guard,Branch.condition,value,hA,hB,hd,and_assoc]

/-- Equivalence at every specialization, including rejection when D specializes to zero. -/
theorem square_iff_root (φ : R →+* ℚ) (A B D : R) (y : K) :
    (φ D ≠ 0 ∧ y^2 = pair (φ A / φ D) (φ B / φ D)) ↔
      ∃ (k : Branch) (w : ℚ), guard k (φ A) (φ B) (φ D) w ∧
        ((polynomial k A B D).map φ).IsRoot w ∧ y = reconstruct k (φ B) (φ D) w := by
  constructor
  · rintro ⟨hd,hy⟩
    obtain ⟨k,t,ht,he⟩ := (four_charts _ _ _).mp hy
    obtain ⟨hg,hv⟩ := (condition_scaled k _ _ _ t hd).mp ht
    exact ⟨k,_,hg,(specialized_root φ k A B D _).mpr hv,he.trans (reconstruct_scaled k _ _ t hd).symm⟩
  · rintro ⟨k,w,hg,hw,hy⟩
    have hd := hg.1
    let t := w/(2*φ D)
    have ht : 2*φ D*t=w := by dsimp [t]; field_simp
    refine ⟨hd,(four_charts _ _ _).mpr ⟨k,t,(condition_scaled k _ _ _ t hd).mpr ?_,?_⟩⟩
    · rw [ht]
      exact ⟨hg,(specialized_root φ k A B D _).mp hw⟩
    · rw [← reconstruct_scaled k _ _ t hd,ht]
      exact hy

end
end Sun28.RootCharts
#print axioms Sun28.RootCharts.polynomial_monic
#print axioms Sun28.RootCharts.specialized_root
#print axioms Sun28.RootCharts.reconstruct_scaled
#print axioms Sun28.RootCharts.condition_scaled
#print axioms Sun28.RootCharts.square_iff_root
