import BoxRecords
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

namespace Sun28.SinglePrime
open ManuscriptV15.Arithmetic Sun28.WeightedSelection Sun28.ContactFactors

def integer (z : Gaussian) : GaussianInt := ⟨z.1,z.2⟩

theorem norm_integer (z : Gaussian) : (integer z).norm=(gaussianNorm z:ℤ) := by
  have n : 0≤z.1^2+z.2^2 := by positivity
  rw [gaussianNorm,Int.natAbs_of_nonneg n,Zsqrtd.norm_def]
  dsimp [integer];ring

private theorem prime_of_norm {z : GaussianInt} (p : ℕ) (prime : p.Prime) (eq : z.norm=(p:ℤ)) :
    Prime z := by
  apply Irreducible.prime
  refine ⟨fun u=>prime.ne_one (by simpa [eq] using Zsqrtd.norm_eq_one_iff.mpr u),?_⟩
  intro a b ab
  have n:=congrArg (fun z : GaussianInt=>z.norm.natAbs) ab
  simp only [Zsqrtd.norm_mul,Int.natAbs_mul,eq,Int.natAbs_natCast] at n
  rcases (Nat.dvd_prime prime).mp (show a.norm.natAbs∣p from ⟨b.norm.natAbs,n⟩) with l|l
  · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp l)
  · rw [l] at n
    exact Or.inr (Zsqrtd.norm_eq_one_iff.mp (by nlinarith [prime.pos] : b.norm.natAbs=1))

private theorem unit_coords (q : GaussianInt) (one : q.norm=1) :
    (q.re=1 ∧ q.im=0) ∨ (q.re= -1 ∧ q.im=0) ∨
      (q.re=0 ∧ q.im=1) ∨ (q.re=0 ∧ q.im= -1) := by
  rw [Zsqrtd.norm_def] at one
  have l : -1≤q.re := by nlinarith only [one,sq_nonneg q.im,sq_nonneg (q.re+1)]
  have u : q.re≤1 := by nlinarith only [one,sq_nonneg q.im,sq_nonneg (q.re-1)]
  have l' : -1≤q.im := by nlinarith only [one,sq_nonneg q.re,sq_nonneg (q.im+1)]
  have u' : q.im≤1 := by nlinarith only [one,sq_nonneg q.re,sq_nonneg (q.im-1)]
  interval_cases hr : q.re <;> interval_cases hi : q.im <;> simp_all

private theorem oriented_divisor {z : Gaussian} {w : GaussianInt} {p : ℕ}
    (prime : p.Prime) (nz : (integer z).norm=(p:ℤ)) (nw : w.norm=(p:ℤ))
    (rz : gaussianCongruent 16 z (9,0)) (rw : w.re ≡ 9 [ZMOD 16])
    (div : integer z∣w) : w=integer z := by
  obtain ⟨q,prod⟩:=div
  have n:=congrArg Zsqrtd.norm prod
  rw [nw,Zsqrtd.norm_mul,nz] at n
  have pos : 0<(p:ℤ) := by exact_mod_cast prime.pos
  have one : q.norm=1 := by nlinarith
  have re:=congrArg Zsqrtd.re prod
  change w.re=z.1*q.re+(-1)*z.2*q.im at re
  have x : z.1%16=9 := rz.1
  have y : z.2%16=0 := rz.2
  change w.re%16=9 at rw
  rcases unit_coords q one with h|h|h|h
  · have e : q=1 := Zsqrtd.ext h.1 h.2
    simpa [e] using prod
  all_goals simp [h.1,h.2] at re; omega

/-- A prime has at most one Gaussian generator in the two specified rays. -/
theorem oriented_unique {z w : Gaussian} {p : ℕ} (prime : p.Prime)
    (hz : gaussianNorm z=p) (hw : gaussianNorm w=p)
    (z16 : gaussianCongruent 16 z (9,0)) (w16 : gaussianCongruent 16 w (9,0))
    (z7 : gaussianCongruent 7 z (1,3)) (w7 : gaussianCongruent 7 w (1,3)) : z=w := by
  have nz : (integer z).norm=(p:ℤ) := (norm_integer z).trans (congrArg (fun n:ℕ=>(n:ℤ)) hz)
  have nw : (integer w).norm=(p:ℤ) := (norm_integer w).trans (congrArg (fun n:ℕ=>(n:ℤ)) hw)
  have div : integer z ∣ integer w*star (integer w) := by
    rw [←Zsqrtd.norm_eq_mul_conj,nw,←nz,Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  rcases (prime_of_norm p prime nz).dvd_or_dvd div with left|right
  · have eq:=oriented_divisor prime nz nw z16 w16.1 left
    exact (Prod.ext (congrArg Zsqrtd.re eq) (congrArg Zsqrtd.im eq)).symm
  · have eq:=oriented_divisor prime nz ((Zsqrtd.norm_conj _).trans nw) z16 w16.1 right
    have im:=congrArg Zsqrtd.im eq
    change -w.2=z.2 at im
    have one : z.2%7=3 := z7.2
    have two : w.2%7=3 := w7.2
    omega

/-- The ray coordinates of a prime tuple depend only on its numerical parameter pair. -/
theorem gaussian_eq_of_pair {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} {a b : Record A d H Y}
    (eq : pair a=pair b) : a.gaussian=b.gaussian := by
  funext r
  have t:=congrArg (fun q : ℕ×ℕ => (q.1:ℤ)+offset (dilation A) r.val*(q.2:ℤ)^2) eq
  have n:=Int.ofNat_inj.mp ((a.values.equation r.val r.property).trans (t.trans (b.values.equation r.val r.property).symm))
  exact oriented_unique (a.values.prime r.val r.property) (a.rays.norm r) ((b.rays.norm r).trans n.symm)
    (a.rays.ray16 r) (b.rays.ray16 r) (a.rays.ray7 r) (b.rays.ray7 r)

end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.norm_integer
#print axioms Sun28.SinglePrime.oriented_unique
#print axioms Sun28.SinglePrime.gaussian_eq_of_pair
