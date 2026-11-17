import GaussianHeader
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

namespace Sun28.CMReduction
open ManuscriptV15.Arithmetic

private theorem norm_as_sum (z : GaussianInt) : z.norm=z.re^2+z.im^2 := by
  rw [Zsqrtd.norm_def]
  ring

theorem archive_norm (z : Gaussian) : (gaussianNorm z:ℤ)=z.1^2+z.2^2 := by
  unfold gaussianNorm
  rw [Int.natCast_natAbs,abs_of_nonneg (by positivity)]

private theorem gaussian_prime_of_prime_norm {p : ℕ} (pp : p.Prime) (z : GaussianInt)
    (hz : z.norm=(p:ℤ)) : Prime z := by
  apply Irreducible.prime
  rw [irreducible_iff]
  constructor
  · intro hu
    have h:=Zsqrtd.norm_eq_one_iff.mpr hu
    rw [hz,Int.natAbs_natCast] at h
    exact pp.ne_one h
  · intro a b he
    have mult : a.norm.natAbs*b.norm.natAbs=p := by
      have eq:=congrArg Int.natAbs hz
      rw [he,Zsqrtd.norm_mul,Int.natAbs_mul,Int.natAbs_natCast] at eq
      exact eq
    have d : a.norm.natAbs∣p := ⟨_,mult.symm⟩
    rcases (Nat.dvd_prime pp).mp d with l|r
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp l)
    · right
      apply Zsqrtd.norm_eq_one_iff.mp
      rw [r] at mult
      exact Nat.eq_of_mul_eq_mul_left pp.pos (by simpa using mult : p*b.norm.natAbs=p*1)

private theorem same_odd_real_of_dvd {p : ℕ} (pp : p.Prime) (z w : GaussianInt)
    (hz : z.norm=(p:ℤ)) (hw : w.norm=(p:ℤ))
    (zeven : z.im%2=0) (wodd : w.re%2=1) (d : z∣w) : w.re=z.re ∨ w.re= -z.re := by
  obtain ⟨k,hk⟩:=d
  have product:=congrArg Zsqrtd.norm hk
  rw [Zsqrtd.norm_mul,hw,hz] at product
  have kp : k.norm=1 := by
    have pos : (0:ℤ)<p := by exact_mod_cast pp.pos
    nlinarith
  have kn := (norm_as_sum k).symm.trans kp
  have kre : -1≤k.re ∧ k.re≤1 := by constructor <;> nlinarith [sq_nonneg k.im]
  have kim : -1≤k.im ∧ k.im≤1 := by constructor <;> nlinarith [sq_nonneg k.re]
  have real := congrArg Zsqrtd.re hk
  rw [Zsqrtd.re_mul] at real
  have zr : k.re = -1 ∨ k.re=0 ∨ k.re=1 := by omega
  have zi : k.im = -1 ∨ k.im=0 ∨ k.im=1 := by omega
  rcases zr with h₁|h₁|h₁ <;> rcases zi with h₂|h₂|h₂ <;>
    simp [h₁,h₂] at kn real <;> omega

/-- The odd coordinate of a rational prime's two-square representation is fixed up to sign. -/
theorem odd_coordinate_unique {p : ℕ} (pp : p.Prime) {a b c e : ℤ}
    (left : a^2+b^2=(p:ℤ)) (right : c^2+e^2=(p:ℤ)) (bEven : b%2=0) (cOdd : c%2=1) :
    c=a ∨ c= -a := by
  let z : GaussianInt:=⟨a,b⟩
  let w : GaussianInt:=⟨c,e⟩
  have hz : z.norm=(p:ℤ) := (norm_as_sum z).trans left
  have hw : w.norm=(p:ℤ) := (norm_as_sum w).trans right
  have products : z*star z=w*star w := by
    rw [← Zsqrtd.norm_eq_mul_conj,← Zsqrtd.norm_eq_mul_conj,hz,hw]
  have d : z∣w*star w := products ▸ dvd_mul_right z (star z)
  rcases (gaussian_prime_of_prime_norm pp z hz).dvd_mul.mp d with d|d
  · exact same_odd_real_of_dvd pp z w hz hw bEven cOdd d
  · exact same_odd_real_of_dvd pp z (star w) hz ((Zsqrtd.norm_conj w).trans hw) bEven cOdd d

end Sun28.CMReduction
#print axioms Sun28.CMReduction.archive_norm
#print axioms Sun28.CMReduction.odd_coordinate_unique
