import TailSummation
import Mathlib.Data.Int.Order.Lemmas

namespace Sun28.SieveTail
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.WeightedSelection Sun28.NormSieve
noncomputable section

variable {A : Fin 3 → ℚ} {d : ℕ} {H Y : ℝ}

def radius (N V : ℕ) (i j : ↥(shifts A)) : ℕ :=
  2*Nat.sqrt (N+max (offset (dilation A) i.val).natAbs (offset (dilation A) j.val).natAbs*V^2)

theorem coordinates (a : Candidate A d H Y) (i : ↥(shifts A)) (N V C : ℕ)
    (hn : a.u≤N) (v : a.v=V) (coef : (offset (dilation A) i.val).natAbs≤C) :
    let W := (Nat.sqrt (N+C*V^2):ℤ)
    |(a.gaussian i).1| ≤ W ∧ |(a.gaussian i).2| ≤ W := by
  have nc : (gaussianNorm (a.gaussian i):ℤ)=(a.gaussian i).1^2+(a.gaussian i).2^2 :=
    Int.natAbs_of_nonneg (by positivity)
  rw [a.rays.norm i,a.values.equation i.val i.property,v] at nc
  have cm : offset (dilation A) i.val ≤ (C:ℤ) :=
    (le_abs_self _).trans (by rw [←Int.natCast_natAbs];exact_mod_cast coef)
  have lim : (a.gaussian i).1^2+(a.gaussian i).2^2 ≤ ((N+C*V^2:ℕ):ℤ) := by
    rw [←nc]
    push_cast
    exact add_le_add (by exact_mod_cast hn) (mul_le_mul_of_nonneg_right cm (sq_nonneg _))
  have sq (t : ℤ) (nt : t^2≤((N+C*V^2:ℕ):ℤ)) :
      |t| ≤ (Nat.sqrt (N+C*V^2):ℤ) := by
    simpa only [Int.sqrt_natCast] using (Int.abs_le_sqrt_iff_sq_le (Int.natCast_nonneg _)).mpr nt
  exact ⟨sq _ (by linarith only [lim,sq_nonneg (a.gaussian i).2]),
    sq _ (by linarith only [lim,sq_nonneg (a.gaussian i).1])⟩

theorem in_interval {n : ℤ} {B : ℕ} (h : |n|≤(B:ℤ)) : n∈interval B :=
  Finset.mem_Ico.mpr ⟨(abs_le.mp h).1, by have k:=(abs_le.mp h).2; omega⟩

theorem actual_chart_box (boxes : CountingBoxes A d H Y) (N V : ℕ) (i j : ↥(shifts A)) :
    chartBox boxes N V (radius N V i j) i j := by
  intro a rec va
  let C := max (offset (dilation A) i.val).natAbs (offset (dilation A) j.val).natAbs
  let W := Nat.sqrt (N+C*V^2)
  have ⟨ai,bi⟩ := coordinates a i N V C (boxes.inBox N a rec).2.1 va (le_max_left _ _)
  have ⟨aj,bj⟩ := coordinates a j N V C (boxes.inBox N a rec).2.1 va (le_max_right _ _)
  change |(a.gaussian i).1|≤(W:ℤ) at ai
  change |(a.gaussian i).2|≤(W:ℤ) at bi
  change |(a.gaussian j).1|≤(W:ℤ) at aj
  change |(a.gaussian j).2|≤(W:ℤ) at bj
  have tr := (abs_add_le (a.gaussian i).1 (a.gaussian j).1).trans (add_le_add ai aj)
  have xx := (abs_sub _ _).trans (add_le_add bi bj)
  have zz := (abs_add_le (a.gaussian i).2 (a.gaussian j).2).trans (add_le_add bi bj)
  have wd : ((radius N V i j:ℕ):ℤ)=(W:ℤ)+W := by simp only [radius,two_mul,W,C,Nat.cast_add]
  refine ⟨Nat.cast_le (α:=ℤ) |>.mp ?_,in_interval ?_,in_interval ?_⟩
  · rw [wd,Int.natCast_natAbs];exact tr
  · rw [wd];exact xx
  · rw [wd];exact zz

/-- The fixed-v saving on the literal weighted-selection records, with the
chart radius proved from the two exact prime norm equations. -/
theorem offdiag_records {N V R : ℕ} (boxes : CountingBoxes A d H Y) (rp : 0 < R)
    (i j : ↥(shifts A)) (ij : i≠j) :
    let B := radius N V i j
    let K := gap i j*(V:ℤ)^2
    let L := 2*(B:ℚ)+1
    ((pairRecords boxes N V R i j).card:ℚ) ≤
      K.natAbs.divisors.card*(8*(Nat.log 2 (K.natAbs+2*B):ℚ)*(L/R+1))*(L*harmonic B+B) :=
  fixed_v_saving boxes N V _ R rp i j ij (actual_chart_box boxes N V i j)

end
end Sun28.SieveTail
#print axioms Sun28.SieveTail.coordinates
#print axioms Sun28.SieveTail.in_interval
#print axioms Sun28.SieveTail.actual_chart_box
#print axioms Sun28.SieveTail.offdiag_records
