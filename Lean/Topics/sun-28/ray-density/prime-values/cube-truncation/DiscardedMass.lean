import ResidueMass
import AffineMassError

namespace Sun28.CubeTruncation
open Sun28.AffinePullback Finset
noncomputable section

/-- Signed discarded mass after summing over all residue classes, before normalization. -/
theorem total_discard (n : ℕ) [NeZero n] (q J h a : ℕ) (hh:0<h)
    (F : ZMod n→ℝ) (M:ℝ) (pos:0≤M) (bound:∀x, |F x|≤M) :
    let k:=J/h
    let X:=∑ rs : Fin a→Fin h, boxSum n q (List.ofFn (fun i=>lengthAt J h (rs i))) F
    let Y:=boxSum n q (List.replicate a k) F
    |X-(h:ℝ)^a*Y| ≤
      n * ((((h:ℝ)*k^2+(2*k+1)*(J%h:ℕ))^a)-((h:ℝ)*k^2)^a)*M^(2^a) := by
  let k:=J/h
  let C:=M^(2^a)
  let X (rs:Fin a→Fin h):=boxSum n q (List.ofFn (fun i=>lengthAt J h (rs i))) F
  let Y:=boxSum n q (List.replicate a k) F
  let d (rs:Fin a→Fin h):=∏ i:Fin a,(lengthAt J h (rs i):ℝ)^2
  have each (rs:Fin a→Fin h) : |X rs-Y| ≤
      ((n:ℝ)*d rs-n*((k:ℝ)^2)^a)*C := by
    simpa [X,Y,d,k,List.ofFn_const] using
      box_discard n q a (fun _=>k) (fun i=>lengthAt J h (rs i)) (fun i=>interval_ge J h (rs i)) F M pos bound
  have card : (∑ _rs:Fin a→Fin h,Y)=(h:ℝ)^a*Y := by simp [nsmul_eq_mul]
  have totald : (∑ rs :Fin a→Fin h,d rs) = ((h:ℝ)*k^2+(2*k+1)*(J%h:ℕ))^a := interval_sum J h a hh
  change |(∑ rs:Fin a→Fin h,X rs) - (h:ℝ)^a*Y| ≤
    n*((((h:ℝ)*k^2+(2*k+1)*(J%h:ℕ))^a)-((h:ℝ)*k^2)^a)*C
  rw [←card,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ rs:Fin a→Fin h, |X rs-Y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ rs:Fin a→Fin h, ((n:ℝ)*d rs-n*((k:ℝ)^2)^a)*C :=
      Finset.sum_le_sum (fun rs _=>each rs)
    _ = _ := by
      rw [←Finset.sum_mul, Finset.sum_sub_distrib, ←Finset.mul_sum, totald]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, mul_pow]
      ring

theorem short_abs_average (n : ℕ) [NeZero n] (q k a : ℕ) (hk : 0<k) (F : ZMod n→ℝ)
    (M:ℝ) (pos:0≤M) (bound:∀x, |F x|≤M) :
    |boxAverage n q (List.replicate a k) F| ≤ M^(2^a) := by
  have u:=box_abs n q a (fun _=>k) F M pos bound
  simp only [List.ofFn_const, Finset.prod_const,Finset.card_univ,Fintype.card_fin] at u
  have nk : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have kp : (0:ℝ)<k := by exact_mod_cast hk
  simp only [boxAverage, intervalMass, List.prod_replicate, Nat.cast_pow, abs_div]
  have hD : (0:ℝ)<n*((k:ℝ)^a)^2 := mul_pos nk (sq_pos_of_pos (pow_pos kp a))
  rw [abs_of_pos hD,div_le_iff₀ hD]
  convert u using 1
  ring

end
end Sun28.CubeTruncation
#print axioms Sun28.CubeTruncation.total_discard
#print axioms Sun28.CubeTruncation.short_abs_average
