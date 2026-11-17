import DiscardedMass

namespace Sun28.CubeTruncation
open Sun28.AffinePullback Finset
noncomputable section

/-- The manuscript's actual signed cube error, with explicit constant and arbitrary interval remainder. -/
theorem localized_error {E n : ℕ} [NeZero n] [NeZero (E*n)] (hE:0<E) (q J a : ℕ)
    (large : E/E.gcd q ≤ J) (t:ZMod (E*n)) (F:ZMod n→ℝ) (M:ℝ) (pos:0≤M)
    (bound:∀x, |F x|≤M) :
    let h:=E/E.gcd q
    let k:=J/h
    |boxAverage (E*n) q (List.replicate a J) (extend E n t F) -
       (1/(h:ℝ))^a*boxAverage n (q/E.gcd q) (List.replicate a k) F / E|
      ≤ 4*a*M^(2^a)/(E*J) := by
  let h:=E/E.gcd q
  let k:=J/h
  let b:=J%h
  let q':=q/E.gcd q
  have hh : 0<h := Nat.div_pos (Nat.le_of_dvd hE (Nat.gcd_dvd_left _ _)) (Nat.gcd_pos_of_pos_left _ hE)
  have hk : 0<k := Nat.div_pos large hh
  have hJ : 0<J := hh.trans_le large
  have nh : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have epos : (0:ℝ)<E := by exact_mod_cast hE
  have jp : (0:ℝ)<J := by exact_mod_cast hJ
  have hb : b<h := Nat.mod_lt J hh
  have dec : J=h*k+b := by rw [add_comm]; exact (Nat.mod_add_div ..).symm
  let X:=boxSum (E*n) q (List.replicate a J) (extend E n t F)
  let Y:=boxSum n q' (List.replicate a k) F
  let Z:=boxAverage (E*n) q (List.replicate a J) (extend E n t F)
  let B:=boxAverage n q' (List.replicate a k) F
  let D:ℝ:=((J:ℝ)^2)^a
  let W:ℝ:=(h:ℝ)*k^2
  let S:ℝ:=W+(2*k+1)*b
  let T:ℝ:=(X-(h:ℝ)^a*Y)/((n:ℝ)*D)
  have sm : intervalMass (List.replicate a J)=D := by simp [intervalMass,D,pow_right_comm]
  have km : intervalMass (List.replicate a k)=((k:ℝ)^2)^a := by simp [intervalMass,pow_right_comm]
  have Dpos : 0<D := by dsimp [D]; positivity
  have denom : 0<(n:ℝ)*D := mul_pos nh Dpos
  have hu : |X-(h:ℝ)^a*Y|≤(n:ℝ)*(S^a-W^a)*M^(2^a) := by
    have flip := total_discard n q' J h a hh F M pos bound
    have changeX := localized_sum hE q J a t F
    rw [branches_sum] at changeX
    dsimp only [X,Y,S,W,b,k]
    rw [changeX]
    exact flip
  have tr : |T| ≤ ((S/(J:ℝ)^2)^a)*M^(2^a) - ((W/(J:ℝ)^2)^a)*M^(2^a) := by
    dsimp only [T]
    rw [abs_div, abs_of_pos denom, div_le_iff₀ denom, div_pow, div_pow]
    change _ ≤ (S^a/D*M^(2^a) - W^a/D*M^(2^a)) * ((n:ℝ)*D)
    convert hu using 1
    field_simp
  have sx : X=(E:ℝ)*n*D*Z := by
    simpa only [X,Z,Nat.cast_mul,sm] using recover_sum q (List.replicate a J) (extend E n t F)
  have sy : Y=(n:ℝ)*((k:ℝ)^2)^a*B := by
    simpa only [Y,B,km] using recover_sum q' (List.replicate a k) F
  have split : (E:ℝ)*Z=(W/(J:ℝ)^2)^a*B+T := by
    dsimp only [T,W]
    rw [div_pow,mul_pow,sx,sy]
    change (E:ℝ)*Z=((h:ℝ)^a*((k:ℝ)^2)^a)/D*B +
        ((E:ℝ)*n*D*Z-(h:ℝ)^a*((n:ℝ)*((k:ℝ)^2)^a*B))/((n:ℝ)*D)
    field_simp
    ring
  change |Z-(1/(h:ℝ))^a*B/E| ≤ 4*a*M^(2^a)/(E*J)
  exact ZInQBlueprint.AffineIntervals.uneven_intervals hh hk hb dec a epos
    (pow_nonneg pos _) (short_abs_average n q' k a hk F M pos bound) tr split

/-- For dimension zero there are no directions, so every J gives the base mean identity. -/
theorem zero_dimensional {E n : ℕ} [NeZero n] [NeZero (E*n)] (hE : 0<E)
    (q : ℕ) (t : ZMod (E*n)) (F : ZMod n → ℝ) :
    boxAverage (E*n) q [] (extend E n t F)=boxAverage n (q/E.gcd q) [] F/E := by
  have e:=localized_average hE q 1 0 (by decide) t F
  simpa [div_eq_inv_mul] using e

end
end Sun28.CubeTruncation
#print axioms Sun28.CubeTruncation.localized_error

#print axioms Sun28.CubeTruncation.zero_dimensional
