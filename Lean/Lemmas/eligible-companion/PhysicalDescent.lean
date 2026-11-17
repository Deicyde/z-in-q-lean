import EllipticDescent
import SignedPole
import QuadraticPivots

namespace CompanionDescent.Physical
open Lean.Grind

private theorem nz {x y : Rat} (hx : x≠0) (hy : y≠0) : x*y≠0 :=
  fun h => (Rat.mul_eq_zero.mp h).elim hx hy

private theorem sqnonneg (q : Rat) : 0≤q^2 := by
  rcases Rat.nonneg_total q with h|h
  · exact Rat.pow_nonneg h
  · have e:=Rat.mul_nonneg h h
    rwa [show -q*(-q)=q^2 by grobner] at e

/-- Scaling the denominator coordinates of both slopes changes the first
coefficient by c². The equality also holds at zero and infinity. -/
theorem scale_first (β c θ : Rat) (hc : c≠0) :
    ProjectiveWeak (β*c^2) θ ↔ ProjectiveWeak β θ := by
  have ic : c*c⁻¹=1 := by grind
  have nc : c⁻¹≠0 := by intro h; rw [h] at ic; grind
  have scale (x s : Rat) : homogeneous (β*c^2) x s=homogeneous β x (c*s) := by
    unfold homogeneous; grobner
  constructor
  · rintro ⟨X,S,B,A,z,hx,hy,e⟩
    exact ⟨X,c*S,B,c*A,z,hx.imp_right (nz hc),hy.imp_right (nz hc),by rwa [scale,scale] at e⟩
  · rintro ⟨X,S,B,A,z,hx,hy,e⟩
    refine ⟨X,c⁻¹*S,B,c⁻¹*A,z,hx.imp_right (nz nc),hy.imp_right (nz nc),?_⟩
    rw [scale,scale,show c*(c⁻¹*S)=S by grobner,show c*(c⁻¹*A)=A by grobner]
    exact e

/-- Normalize the literal coefficients from FixedZero.exact_weak. In the
source 17*b=β*c² and 289-17*b=17²*θ. -/
theorem fixed_zero_projective (b β θ c : Rat) (hβ : 0<β) (nβ : nonsquare β)
    (hc : c≠0) (first : 17*b=β*c^2) (second : 289-17*b=289*θ) :
    WitnessTransfer.FixedZero.PsiZero b ↔ ProjectiveWeak β θ := by
  have ic : c*c⁻¹=1 := by grind
  have nb : ∀ q : Rat, q^2≠17*b := by
    intro q h
    apply nβ (q*c⁻¹)
    calc _ = q^2*(c⁻¹)^2 := by grobner
         _ = _ := by rw [h,first]; grobner
  have hp : 0<c^2 := by
    have hn:=sqnonneg c
    have n2 := nz hc hc
    by_cases e : 0<c^2
    · exact e
    · have z : c^2=0 := by grind
      exact False.elim (n2 (by grobner))
  have bpos := Rat.mul_pos hβ hp
  have hm : ∀ q : Rat, q^2≠ -3*(17*b) := by
    intro q h; have hq:=sqnonneg q; grind
  have theta : 1-(17*b)*(1/17:Rat)^2=θ := by grobner
  have bridge : WeakBisection.Weak (17*b) (1/17) ↔ ProjectiveWeak (17*b) θ := by
    change ProjectiveWeak (17*b) (1-(17*b)*(1/17:Rat)^2) ↔ _
    rw [theta]
  exact (SignedPole.source_projective b nb hm).trans
    (bridge.trans (by rw [first]; exact scale_first β c θ hc))

/-- The original four-witness row and its elliptic replacement have the same
rational solutions after projection, with both squareclasses normalized. -/
theorem fixed_zero_iff_elliptic (b β θ c : Rat) (hβ : 0<β) (nβ : nonsquare β)
    (hθ : 0<θ) (nθ : nonsquare θ) (hc : c≠0)
    (first : 17*b=β*c^2) (second : 289-17*b=289*θ) :
    WitnessTransfer.FixedZero.PsiZero b ↔ EllipticFibre β θ :=
  (fixed_zero_projective b β θ c hβ nβ hc first second).trans
    (projective_iff_elliptic β θ hβ nβ hθ nθ)

/-- A square second coefficient already supplies both slopes at infinity. -/
theorem fixed_zero_iff_square_or_elliptic (b β θ c : Rat) (hβ : 0<β) (nβ : nonsquare β)
    (hθ : 0<θ) (hc : c≠0) (first : 17*b=β*c^2) (second : 289-17*b=289*θ) :
    WitnessTransfer.FixedZero.PsiZero b ↔ (∃ q : Rat, q^2=θ) ∨ EllipticFibre β θ := by
  by_cases hs : ∃ q : Rat, q^2=θ
  · refine ⟨fun _ => Or.inl hs,fun _ => ?_⟩
    obtain ⟨q,eq⟩ := hs
    apply (fixed_zero_projective b β θ c hβ nβ hc first second).mpr
    rw [←eq]; exact square_coefficient β q
  · have nθ : nonsquare θ := fun q eq => hs ⟨q,eq⟩
    have core := fixed_zero_iff_elliptic b β θ c hβ nβ hθ nθ hc first second
    exact ⟨fun h => Or.inr (core.mp h),fun h => core.mpr (h.resolve_left hs)⟩

def beta : Rat := 412690661369
def gate : Rat := 28560378599647930000
def theta (W : Rat) := 1-W^2/(17*gate)

/-- The two physical prepared rows supply nonzero W and the strict real bound.
The numerical first class is proved nonsquare within this theorem. -/
theorem input_one (W : Rat) (nW : W≠0) (bound : W^2<17*gate) :
    WitnessTransfer.FixedZero.PsiZero (W^2/gate) ↔
      (∃ q : Rat, q^2=theta W) ∨ EllipticFibre beta (theta W) := by
  have nβ : nonsquare beta := fun q => CircuitTransport.Quadratic.no_square_in_gap
    (n:=412690661369) (k:=642410) (by decide) (by decide) q
  have ng : gate≠0 := by unfold gate; decide
  have nfac : 34300/gate≠0 := by
    intro eq
    have row : (34300/gate)*gate=34300 := Rat.div_mul_cancel ng
    rw [eq] at row
    grind
  have nc : (34300/gate)*W≠0 := nz nfac nW
  have scale : 17*(W^2/gate)=beta*((34300/gate)*W)^2 := by unfold gate beta; grobner
  have scales : 289-17*(W^2/gate)=289*theta W := by unfold theta gate; grobner
  have hθ : 0<theta W := by
    unfold theta gate
    unfold gate at bound
    grind
  exact fixed_zero_iff_square_or_elliptic _ beta _ _ (by unfold beta; decide) nβ hθ nc scale scales

#print axioms scale_first
#print axioms fixed_zero_projective
#print axioms fixed_zero_iff_elliptic
#print axioms fixed_zero_iff_square_or_elliptic
#print axioms input_one
end CompanionDescent.Physical
