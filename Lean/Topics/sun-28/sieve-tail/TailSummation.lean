import CandidateTail
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Sun28.SieveTail
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.WeightedSelection
noncomputable section

/-- A product of two explicit progression counts. When p divides g the size
of g itself supplies the large-prime saving. -/
theorem slice_cutoff {B g q p R : ℕ} (gp : 0 < g) (_qp : 0 < q) (rp : 0 < R) (large : R < p) :
    sliceBound B g q p ≤ 2*((2*(B:ℚ)+1)/R+1)*((2*(B:ℚ)+1)/q+1) := by
  let L : ℚ := 2*(B:ℚ)+1
  have lp : 0≤L := by dsimp [L];positivity
  have pos : 0<(R:ℚ) := by exact_mod_cast rp
  have hp : R≤p := large.le
  unfold sliceBound
  change (if p∣g then L/g+1 else 2*(L/(g*p)+1))*(L/q+1)≤_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  split_ifs with div
  · have le : (R:ℚ)≤g := by exact_mod_cast hp.trans (Nat.le_of_dvd gp div)
    have e:=div_le_div_of_nonneg_left lp pos le
    change L/g+1≤2*(L/R+1)
    linarith [div_nonneg lp pos.le]
  · have bound : R≤g*p := hp.trans (by simpa using Nat.mul_le_mul_right p gp)
    have e:=div_le_div_of_nonneg_left lp pos (show (R:ℚ)≤(g:ℚ)*p by exact_mod_cast bound)
    change 2*(L/(g*p)+1)≤2*(L/R+1)
    linarith

theorem prime_count_uniform (K : ℤ) {t : ℤ} {B : ℕ} (ht : t.natAbs≤B)
    (R : ℕ) :
    ((K+2*t).natAbs.primeFactors.filter (fun p => R<p)).card ≤ Nat.log 2 (K.natAbs+2*B) := by
  by_cases zero : K+2*t=0
  · simp [zero]
  have norm : (K+2*t).natAbs≤K.natAbs+2*B := calc
    _ ≤ K.natAbs+(2*t).natAbs := Int.natAbs_add_le _ _
    _ = K.natAbs+2*t.natAbs := by rw [Int.natAbs_mul];rfl
    _ ≤ _ := by omega
  exact (Finset.card_filter_le ..).trans
    ((prime_divisors_card (Int.natAbs_ne_zero.mpr zero)).trans (Nat.log_mono_right norm))

theorem sum_progression_cost (B Q : ℕ) (small : Q≤B) :
    (∑ q∈Finset.Icc 1 Q,((2*(B:ℚ)+1)/q+1)) ≤ (2*(B:ℚ)+1)*harmonic B+B := by
  let L:ℚ:=2*(B:ℚ)+1
  have grow : (∑ q∈Finset.Icc 1 Q,((2*(B:ℚ)+1)/q+1))≤∑ q∈Finset.Icc 1 B,((2*(B:ℚ)+1)/q+1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (le_refl _) small)
      (by intros;positivity)
  apply grow.trans_eq
  rw [Finset.sum_add_distrib,harmonic_eq_sum_Icc,Finset.mul_sum]
  simp [div_eq_mul_inv]

/-- Explicit saving at each fixed v, even if the chosen prime exceeds the
coordinate box. There is no lattice, integral-polynomial or sieve input. -/
theorem fixed_v_saving {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}
    (boxes : CountingBoxes A d H Y) (N V B R : ℕ) (rp : 0 < R)
    (i j : ↥(shifts A)) (ij : i≠j) (bounds : chartBox boxes N V B i j) :
    let K := gap i j*(V:ℤ)^2
    let L := 2*(B:ℚ)+1
    ((pairRecords boxes N V R i j).card:ℚ) ≤
      K.natAbs.divisors.card * (8*(Nat.log 2 (K.natAbs+2*B):ℚ)*(L/R+1))*(L*harmonic B+B) := by
  classical
  let K := gap i j*(V:ℤ)^2
  let L := 2*(B:ℚ)+1
  let D : ℚ := Nat.log 2 (K.natAbs+2*B)
  let C := 8*D*(L/R+1)
  have cp : 0≤C := by dsimp [C,D,L];positivity
  dsimp only
  apply (fixed_v_candidate_bound boxes N V B R i j ij bounds).trans
  change _ ≤ ((K.natAbs.divisors.card:ℚ)*C)*(L*harmonic B+B)
  rw [mul_assoc]
  calc
    _ ≤ ∑ _g∈K.natAbs.divisors,C*(L*harmonic B+B) := by
      apply Finset.sum_le_sum
      intro g hg
      have gp := Nat.pos_of_mem_divisors hg
      calc
        _ ≤ ∑ q∈Finset.Icc 1 (B/g), C*(L/q+1) := by
          apply Finset.sum_le_sum
          intro q hq
          obtain ⟨qp,qmax⟩ := Finset.mem_Icc.mp hq
          have bound : g*q≤B := by simpa [mul_comm] using (Nat.le_div_iff_mul_le gp).mp qmax
          let val := 4*(L/R+1)*(L/q+1)
          have vp : 0≤val := by dsimp [val,L];positivity
          have hsign (e : Bool) :
             (∑ p∈(K+2*signedCoordinate e g q).natAbs.primeFactors.filter (fun p => R<p),2*sliceBound B g q p)≤D*val := by
            let S := (K+2*signedCoordinate e g q).natAbs.primeFactors.filter (fun p => R<p)
            change (∑ p∈S,2*sliceBound B g q p) ≤ _
            have st : (signedCoordinate e g q).natAbs ≤ B := by
              cases e <;> simpa only [signedCoordinate,ite_true,Bool.false_eq_true,ite_false,Int.natAbs_neg,Int.natAbs_natCast] using bound
            have cnt : (S.card:ℚ) ≤ D := Nat.cast_le.mpr (prime_count_uniform K st R)
            calc _ ≤ ∑ _p∈S,val := by
                   apply Finset.sum_le_sum
                   intro p hp
                   have h:=slice_cutoff (B:=B) (g:=g) (q:=q) gp qp rp (Finset.mem_filter.mp hp).2
                   dsimp only [val,L]
                   linarith only [h]
                 _ = (S.card:ℚ)*val := by simp
                 _ ≤ _ := mul_le_mul_of_nonneg_right cnt vp
          change (∑ e : Bool,_) ≤ _
          calc _ ≤ ∑ _e : Bool,D*val := Finset.sum_le_sum fun e _ => hsign e
               _ = _ := by simp [C,val];ring
        _ = C*∑ q∈Finset.Icc 1 (B/g),(L/q+1) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_progression_cost B _ (Nat.div_le_self B g)) cp
    _ = _ := by simp

end
end Sun28.SieveTail
#print axioms Sun28.SieveTail.slice_cutoff
#print axioms Sun28.SieveTail.prime_count_uniform
#print axioms Sun28.SieveTail.sum_progression_cost
#print axioms Sun28.SieveTail.fixed_v_saving
