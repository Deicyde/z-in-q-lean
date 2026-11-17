import LocalizedAverage
import AffineMassError

namespace ZInQBlueprint.AffineIntervals
open Sun28.AffinePullback Finset
noncomputable section

/-- If the interval length is a multiple of the residue modulus, every branch
has exactly k points. The localization has no boundary error. -/
theorem aligned_localized_average {E n : ℕ} [NeZero n] [NeZero (E*n)] (hE : 0<E)
    (q k a : ℕ) (hk : 0<k) (t : ZMod (E*n)) (F : ZMod n → ℝ) :
    let h := E/E.gcd q
    boxAverage (E*n) q (List.replicate a (h*k)) (extend E n t F) =
      (1/(E:ℝ))*(1/(h:ℝ))^a*boxAverage n (q/E.gcd q) (List.replicate a k) F := by
  let h := E / E.gcd q
  have hh : 0<h := Nat.div_pos (Nat.le_of_dvd hE (Nat.gcd_dvd_left E q)) (Nat.gcd_pos_of_pos_left q hE)
  have J := Nat.mul_pos hh hk
  have same (r : Fin h) : lengthAt (h*k) h r=k := by simp [lengthAt,hh.ne',Nat.mul_comm h k]
  have solve:=localized_average hE q (h*k) a J t F
  change boxAverage (E*n) q (List.replicate a (h*k)) (extend E n t F) =
    (1/(E:ℝ))*(1/(h:ℝ))^a*boxAverage n (q/E.gcd q) (List.replicate a k) F
  rw [solve]
  change _ * (∑ rs : Fin a→Fin h, (∏ i:Fin a, ((lengthAt (h*k) h (rs i):ℝ)/(h*k:ℕ))^2) *
    boxAverage n (q/E.gcd q) (List.ofFn fun i => lengthAt (h*k) h (rs i)) F) = _
  simp_rw [same]
  have hp : (h:ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have kp : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have frac : (k:ℝ)/((h*k:ℕ):ℝ) = 1/(h:ℝ) := by push_cast; field_simp
  rw [frac]
  simp [Finset.sum_const, List.ofFn_const, nsmul_eq_mul]
  ring_nf
  field_simp
  rw [pow_mul, one_div_pow]
  field_simp

end
end ZInQBlueprint.AffineIntervals
#print axioms ZInQBlueprint.AffineIntervals.aligned_localized_average
