import ThreeAdicSection

namespace Sun28.LocalQuartics
open Polynomial
noncomputable section

def quarticForm {R : Type*} [CommRing R] (b U V : R) : R :=
  (U^2-b*V^2)*(U^2+3*b*V^2)

/-- A point on an affine chart of the smooth projective quartic, with
integral coordinates and a unit in at least one direction. -/
def LocalCover (p b k : ℕ) [Fact p.Prime] : Prop :=
  ∃ U V Y : ℤ_[p], (IsUnit U ∨ IsUnit V) ∧ Y^2=(k:ℤ_[p])*quarticForm (b:ℤ_[p]) U V

theorem square_residue_lift {p : ℕ} [hp : Fact p.Prime] (odd : p≠2)
    {A : ℤ_[p]} {x : ZMod p} (unit : x≠0) (res : PadicInt.toZMod A=x^2) :
    ∃ y : ℤ_[p], y^2=A := by
  let t : ℤ_[p] := (x.val:ℕ)
  have rt : PadicInt.toZMod t=x := by simp [t]
  have small : ‖t^2-A‖<1 := by
    apply PadicInt.not_isUnit_iff.mp
    change t^2-A ∈ IsLocalRing.maximalIdeal ℤ_[p]
    rw [←PadicInt.ker_toZMod,RingHom.mem_ker]
    simp [rt,res]
  have unitT : ‖t‖=1 := by
    apply PadicInt.isUnit_iff.mp
    by_contra h
    change t ∈ IsLocalRing.maximalIdeal ℤ_[p] at h
    rw [←PadicInt.ker_toZMod,RingHom.mem_ker,rt] at h
    exact unit h
  have n2 : ‖(2:ℤ_[p])‖=1 := (PadicInt.norm_natCast_eq_one_iff (p:=p) (n:=2)).mpr
    (hp.out.coprime_iff_not_dvd.mpr (fun d=>odd ((Nat.dvd_prime Nat.prime_two).mp d |>.resolve_left hp.out.ne_one)))
  let f : Polynomial ℤ_[p] := X^2-C A
  have ev (u : ℤ_[p]) : f.aeval u=u^2-A := by simp [f]
  have der : f.derivative.aeval t=2*t := by simp [f,derivative_pow]
  have cond : ‖f.aeval t‖<‖f.derivative.aeval t‖^2 := by
    simpa only [ev,der,norm_mul,n2,unitT,one_mul,one_pow] using small
  obtain ⟨y,e,_,_,_⟩:=hensels_lemma cond
  exact ⟨y,sub_eq_zero.mp ((ev y).symm.trans e)⟩

theorem dyadic_one_mod_eight (k : ℕ) (h : k≡1 [MOD 8]) :
    ∃ y : ℤ_[2], y^2=k := by
  have hz : (8:ℤ) ∣ (k:ℤ)-1 := Int.modEq_iff_dvd.mp (by exact_mod_cast h.symm)
  obtain ⟨w,hw⟩:=hz
  have diff : (1:ℤ_[2])-k= -((2:ℤ_[2])^3*(w:ℤ_[2])) := by
    have e : (k:ℤ_[2])-1=8*(w:ℤ_[2]) := by exact_mod_cast hw
    linear_combination -e
  have n2 : ‖(2:ℤ_[2])‖=(2:ℝ)⁻¹ := PadicInt.norm_p
  let f : Polynomial ℤ_[2] := X^2-C (k:ℤ_[2])
  have ev (u:ℤ_[2]) : f.aeval u=u^2-k := by simp [f]
  have der : f.derivative.aeval (1:ℤ_[2])=2 := by simp [f,derivative_pow]
  have cond : ‖f.aeval (1:ℤ_[2])‖<‖f.derivative.aeval (1:ℤ_[2])‖^2 := by
    rw [ev,one_pow,diff,norm_neg,norm_mul,norm_pow,der,n2]
    nlinarith [PadicInt.norm_le_one (p:=2) (w:ℤ_[2])]
  obtain ⟨y,e,_,_,_⟩:=hensels_lemma cond
  exact ⟨y,sub_eq_zero.mp ((ev y).symm.trans e)⟩

theorem at_infinity {p b k : ℕ} [Fact p.Prime] (H : ∃ y : ℤ_[p],y^2=k) : LocalCover p b k := by
  obtain ⟨y,hy⟩:=H
  exact ⟨1,0,y,Or.inl isUnit_one,by simpa [quarticForm] using hy⟩

theorem at_root {p b k : ℕ} [Fact p.Prime] (H : ∃ u : ℤ_[p],u^2=b ∨ u^2= -3*(b:ℤ_[p])) :
    LocalCover p b k := by
  obtain ⟨u,h|h⟩:=H
  · exact ⟨u,1,0,Or.inr isUnit_one,by simp [quarticForm,h]⟩
  · exact ⟨u,1,0,Or.inr isUnit_one,by simp [quarticForm,h]⟩

end
end Sun28.LocalQuartics
#print axioms Sun28.LocalQuartics.square_residue_lift
#print axioms Sun28.LocalQuartics.dyadic_one_mod_eight
#print axioms Sun28.LocalQuartics.at_infinity
#print axioms Sun28.LocalQuartics.at_root
