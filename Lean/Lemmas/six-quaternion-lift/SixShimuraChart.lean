import SixLabelledClass
import MarkedQuotientChart

/-! On the x=4 chart, the quotient by w₃ remembers z/y. We work on
the ordinary locus y z ≠ 0. A Galois-equivariant map from this quotient's
geometric points to the actual real-labelled moduli classes suffices. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.QuaternionLift
open ThetaClass QuaternionMarking NormalDescent AbelianModel CoarseConic
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The open chart x=4 on the Baba–Granath conic. -/
@[ext] structure ConicPoint where
  y : Qbar
  z : Qbar
  onCurve : 4^2 + 3*y^2 + z^2 = 0
  y_ne : y ≠ 0
  z_ne : z ≠ 0

def ConicPoint.w3 (p : ConicPoint) : ConicPoint where
  y := -p.y
  z := -p.z
  onCurve := by rw [neg_sq,neg_sq]; exact p.onCurve
  y_ne := neg_ne_zero.mpr p.y_ne
  z_ne := neg_ne_zero.mpr p.z_ne

def ConicPoint.conjugate (σ : Gal) (p : ConicPoint) : ConicPoint where
  y := σ p.y
  z := σ p.z
  onCurve := by simpa [map_ofNat] using congrArg σ p.onCurve
  y_ne := (map_ne_zero_iff σ σ.injective).mpr p.y_ne
  z_ne := (map_ne_zero_iff σ σ.injective).mpr p.z_ne

def ConicPoint.quotientCoordinate (p : ConicPoint) := 3 * p.z / p.y

/-- The map to the w₃-quotient separates its two-point orbits on this chart. -/
theorem quotient_eq_iff (p q : ConicPoint) :
    p.quotientCoordinate = q.quotientCoordinate ↔ q = p ∨ q = p.w3 := by
  constructor
  · intro e
    have t : p.z * q.y = q.z * p.y := by
      change 3*p.z/p.y = 3*q.z/q.y at e
      have n := (div_eq_div_iff p.y_ne q.y_ne).mp e
      linear_combination n / 3
    have b : p.y^2 = q.y^2 := by
      linear_combination (p.y^2 * q.onCurve - q.y^2 * p.onCurve +
        (p.z*q.y + q.z*p.y)*t) / 16
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp b with b|b
    · left
      apply ConicPoint.ext b.symm
      rw [b] at t
      exact (mul_right_cancel₀ q.y_ne t).symm
    · right
      have e' : q.y = -p.y := by rw [b,neg_neg]
      apply ConicPoint.ext e'
      rw [e'] at t
      apply mul_right_cancel₀ p.y_ne
      change q.z * p.y = -p.z * p.y
      linear_combination -t
  · rintro (rfl|rfl)
    · rfl
    · simp [ConicPoint.quotientCoordinate,ConicPoint.w3]

structure FibrePoint (u : ℚ) (p : ConicPoint) : Prop where
  y_square : p.y^2 = 9 * (SixContact.J u : Qbar)
  z_square : p.z^2 = -27 * (SixContact.J u : Qbar) - 16

theorem fibre_nonempty {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    ∃ p : ConicPoint, FibrePoint u p := by
  obtain ⟨y,hy⟩ := IsAlgClosed.exists_pow_nat_eq (9*(SixContact.J u : Qbar)) (by decide : 0<2)
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (-27*(SixContact.J u : Qbar)-16) (by decide : 0<2)
  have jn : (SixContact.J u : Qbar) ≠ 0 := by exact_mod_cast (unmarked_range hu).2.ne
  have zn : -27*(SixContact.J u : Qbar)-16 ≠ 0 := by
    exact_mod_cast (show -27*SixContact.J u-16 ≠ 0 by linarith [(unmarked_range hu).1])
  refine ⟨⟨y,z,?_,?_,?_⟩,hy,hz⟩
  · linear_combination 3*hy + hz
  · intro y0
    rw [y0] at hy
    simp [jn] at hy
  · intro z0
    rw [z0] at hz
    simp only [zero_pow (by decide : 2 ≠ 0)] at hz
    exact zn hz.symm

theorem coordinate_conjugate (σ : Gal) (p : ConicPoint) :
    (p.conjugate σ).quotientCoordinate = σ p.quotientCoordinate := by
  simp [ConicPoint.quotientCoordinate,ConicPoint.conjugate,map_ofNat]

theorem galois_orbit (p : ConicPoint) (σ : Gal) :
    σ p.quotientCoordinate = p.quotientCoordinate ↔ p.conjugate σ = p ∨ p.conjugate σ = p.w3 := by
  rw [← coordinate_conjugate,← quotient_eq_iff]
  exact eq_comm

theorem fibre_orbit {u : ℚ} (hu : u ∉ ZInQ.contactSet) {p : ConicPoint}
    (hp : FibrePoint u p) (σ : Gal) : p.conjugate σ = p ∨ p.conjugate σ = p.w3 := by
  obtain ⟨_,_,a,ha,_⟩ := marked_quotient_coordinate hu hp.y_square hp.z_square
  exact (galois_orbit p σ).mp (by change σ (3*p.z/p.y) = 3*p.z/p.y; rw [← ha]; simp)

/-- The geometric-point content of the canonical model and the forgetful
map to the moduli problem for R₃. Both identities concern coarse classes. -/
structure ShimuraClassMap where
  value : ConicPoint → ModuliClass
  rational : ∀ (σ : Gal) (p : ConicPoint), value (p.conjugate σ) = conjugateModuli σ (value p)
  forget_w3 : ∀ p : ConicPoint, value p.w3 = value p

theorem fixed_of_coordinate (U : ShimuraClassMap) (p : ConicPoint) (σ : Gal)
    (fixes : σ p.quotientCoordinate = p.quotientCoordinate) :
    U.value p = conjugateModuli σ (U.value p) := by
  rw [← U.rational]
  rcases (galois_orbit p σ).mp fixes with h|h
  · rw [h]
  · rw [h,U.forget_w3]

end
end ZInQBlueprint.QuaternionLift
#print axioms ZInQBlueprint.QuaternionLift.quotient_eq_iff
#print axioms ZInQBlueprint.QuaternionLift.fibre_nonempty
#print axioms ZInQBlueprint.QuaternionLift.galois_orbit
#print axioms ZInQBlueprint.QuaternionLift.fibre_orbit
#print axioms ZInQBlueprint.QuaternionLift.fixed_of_coordinate
