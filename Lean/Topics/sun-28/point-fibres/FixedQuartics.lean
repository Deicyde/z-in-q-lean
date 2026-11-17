import RatioResidual
import ObstructedSection

namespace Sun28.PointFibres
open Sun28.PointDescent Sun28.PrescribedPoints Sun28.PairedClasses
noncomputable section

/-- Both degree-two factors split in the same quadratic algebra obtained by adjoining √b. -/
def ratioPolynomial (b t k : ℚ) : ℚ :=
  let r:=b*t^2
  ((k-4*b*t)^2-b*(r+3)^2)*((k+4*b*t)^2-b*(r+3)^2)

private def C (b r : ℚ):=b*(r-1)*(r-9)

private theorem polynomial_identity (b t k : ℚ) :
    let r:=b*t^2
    ratioPolynomial b t k=(k^2+C b r)^2-4*b*k^2*(r+3)^2 := by
  dsimp [ratioPolynomial,C]
  ring

def SplitFibre (b θ t : ℚ) : Prop :=
  ∃ k h : ℚ, k≠0 ∧ h≠0 ∧ θ*h^2=ratioPolynomial b t k

/-- Rational points of the diagonal pencil are rational points of an explicit binary quartic. -/
theorem ratio_iff_split {b θ t : ℚ} (bp : 0<b) (r1 : b*t^2≠1) (r9 : b*t^2≠9) :
    RatioCover b θ t ↔ SplitFibre b θ t := by
  let r:=b*t^2
  have rp : 0≤r:=mul_nonneg bp.le (sq_nonneg t)
  have ln : r+3≠0:=by linarith
  have n : C b r≠0:=mul_ne_zero (mul_ne_zero bp.ne' (sub_ne_zero.mpr r1)) (sub_ne_zero.mpr r9)
  constructor
  · rintro ⟨a,c,z,cn,one,two⟩
    change z^2=16*b*r+(r+3)^2*θ*c^2 at two
    let k:=(r+3)*a+z
    have conj : k*((r+3)*a-z)=C b r:=by
      dsimp [k,C];linear_combination (r+3)^2*one-two
    have kn : k≠0:=fun e=>n (by rw [←conj,e,zero_mul])
    have den : 2*k*(r+3)≠0:=mul_ne_zero (mul_ne_zero (by norm_num) kn) ln
    have ak : k^2+C b r=(2*k*(r+3))*a:=by rw [←conj];dsimp [k];ring
    refine ⟨k,(2*k*(r+3))*c,kn,mul_ne_zero den cn,?_⟩
    rw [polynomial_identity]
    change θ*((2*k*(r+3))*c)^2=(k^2+C b r)^2-4*b*k^2*(r+3)^2
    rw [ak]
    linear_combination -(2*k*(r+3))^2*one
  · rintro ⟨k,h,kn,hn,E⟩
    rw [polynomial_identity] at E
    change θ*h^2=(k^2+C b r)^2-4*b*k^2*(r+3)^2 at E
    let den:=2*k*(r+3)
    have dn : den≠0:=mul_ne_zero (mul_ne_zero (by norm_num) kn) ln
    refine ⟨(k^2+C b r)/den,h/den,(k^2-C b r)/(2*k),div_ne_zero hn dn,?_,?_⟩
    · field_simp
      dsimp [den]
      linear_combination -E
    · change ((k^2-C b r)/(2*k))^2=16*b*r+(r+3)^2*θ*(h/den)^2
      dsimp [den];field_simp
      unfold C at E ⊢
      linear_combination -E

theorem split_separates : SplitFibre 17 577 3 ∧ ¬AuxiliaryCover 17 577 ∧ NonzeroPair 17 577 := by
  refine ⟨(ratio_iff_split (b:=17) (t:=3) (by norm_num) (by norm_num) (by norm_num)).mp ?_,section_577⟩
  exact ⟨-55/12,1/12,373,by norm_num,by norm_num,by norm_num⟩

end
end Sun28.PointFibres
#print axioms Sun28.PointFibres.ratio_iff_split
#print axioms Sun28.PointFibres.split_separates
