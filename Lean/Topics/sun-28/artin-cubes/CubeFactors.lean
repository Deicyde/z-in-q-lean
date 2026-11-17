import CubeDensity
import OrdinaryFactors

namespace Sun28.ArtinCube
open Finset
open scoped Classical
open Sun28.PrimeMass
open private power_bound from OrdinaryFactors
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} [Fact p.Prime]

def factor (S : Finset (Finset ι)) (q : ZMod p) (b : Finset ι → ZMod p) : ℝ :=
  rate S q b / (1-1/(p:ℝ))^S.card

private theorem normalize {k : ℕ} {x r : ℝ} (hn : 0 ≤ x) (h1 : x < 1)
    (small : (k:ℝ)*x ≤ 1/2) (lo : 1-(k:ℝ)*x ≤ r) {E : ℝ}
    (ep : 0 ≤ E) (hi : r ≤ 1-(k:ℝ)*x+E) :
    -2*((k:ℝ)*x)^2 ≤ r/(1-x)^k-1 ∧ r/(1-x)^k-1 ≤ 2*E := by
  let den := (1-x)^k
  have dp : 0<den := pow_pos (sub_pos.mpr h1) _
  have be : 1-(k:ℝ)*x ≤ den := by
    simpa [den,sub_eq_add_neg] using (one_add_mul_le_pow (show -2 ≤ -x by linarith) k)
  have half : 1/2 ≤ den := by linarith
  have second : den ≤ 1-(k:ℝ)*x+((k:ℝ)*x)^2 := power_bound k hn h1.le
  change -2*((k:ℝ)*x)^2 ≤ r/den-1 ∧ r/den-1 ≤ 2*E
  constructor
  · apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ dp).mpr
    nlinarith only [lo,second,mul_le_mul_of_nonneg_right half (sq_nonneg ((k:ℝ)*x))]
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ dp).mpr
    nlinarith only [hi,be,mul_le_mul_of_nonneg_right half ep]

/-- At a good prime the normalized local factor differs from one by at most 2(k/p)². -/
theorem factor_good (S : Finset (Finset ι)) (q : ZMod p) (non : q ≠ 0)
    (b : Finset ι → ZMod p) (cap : 2*S.card ≤ p) :
    |factor S q b-1| ≤ 2*((S.card:ℝ)/p)^2 := by
  have pr : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have pp : 1 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have small : (S.card:ℝ)/p ≤ 1/2 := by
    have twice : (S.card:ℝ)*2 ≤ p := by exact_mod_cast (show S.card*2 ≤ p by omega)
    apply (div_le_iff₀ pr).mpr
    linarith
  have ck : (S.card.choose 2:ℝ) ≤ (S.card:ℝ)^2 := by exact_mod_cast Nat.choose_le_pow S.card 2
  have good := rate_good S q non b
  have inc : (S.card.choose 2:ℝ)/(p:ℝ)^2 ≤ ((S.card:ℝ)/p)^2 := by rw [div_pow];gcongr
  have h := normalize (k:=S.card) (x:=1/(p:ℝ)) (by positivity) ((div_lt_one pr).mpr pp)
    (by simpa only [mul_one_div] using small)
    (by simpa only [mul_one_div] using (rate_bounds S q b).1) (sq_nonneg ((S.card:ℝ)/p))
    (by simp only [mul_one_div];linarith only [good,inc])
  rw [abs_le]
  simpa only [factor,mul_one_div,neg_mul] using h

/-- At primes dividing the step one only needs a first-order estimate. -/
theorem factor_any (S : Finset (Finset ι)) (q : ZMod p) (b : Finset ι → ZMod p)
    (cap : 2*S.card ≤ p) : |factor S q b-1| ≤ 2*((S.card:ℝ)/p) := by
  have pr : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have pp : 1 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have twice : (S.card:ℝ)*2 ≤ p := by exact_mod_cast (show S.card*2 ≤ p by omega)
  have small : (S.card:ℝ)/p ≤ 1/2 := (div_le_iff₀ pr).mpr (by linarith)
  have non : 0 ≤ (S.card:ℝ)/p := by positivity
  have lo := (rate_bounds S q b).1
  have h := normalize (k:=S.card) (x:=1/(p:ℝ)) (by positivity) ((div_lt_one pr).mpr pp)
    (by simpa only [mul_one_div] using small) (by simpa only [mul_one_div] using lo) non
    (by simp only [mul_one_div,sub_add_cancel];exact (rate_bounds S q b).2)
  simp only [mul_one_div] at h
  rw [abs_le];refine ⟨?_,h.2⟩
  exact le_trans (by nlinarith only [mul_le_mul_of_nonneg_right small non,non]) h.1

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.factor_good
#print axioms Sun28.ArtinCube.factor_any
