import PrimeTail
import RowApplication

namespace Sun28.PrimeMass
open Sun28.SinglePrime Sun28.ContactFactors Sun28.WeightedSelection Sun28.MediumSieve Finset Filter Topology
open scoped Classical
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

/-- The middle-prime coefficient gains a factor of the logarithm of the cutoff. -/
theorem sharp_transfer {T : Finset ℕ} {κ L J : ℕ} {C : ℝ} (two : 2≤L)
    (cn : 0≤C) (count : PrimeRow A d H Y T κ L J C) : LogRow A d H Y T κ L J (C*(4*Real.log 4)/Real.log L) := by
  intro j large
  obtain ⟨D,dn,rows⟩:=count j large
  have eps:=(poly_error A D dn).eventually_lt_const (show 0<1/((j:ℝ)+1) by positivity)
  filter_upwards [rows,eps] with t counts small
  let N:=lengthAt t
  let W:=rowWidth j N
  let S:=box (A:=A) (d:=d) (H:=H) (Y:=Y) N W
  let X:ℝ:=(N:ℝ)*W
  let G:ℝ:=growthBound A t
  let k:=(shifts A).card
  let R:=logCutoff A t
  let P:=places L R
  let E:ℝ:=D*X/2^t
  have gn : 0<G := by dsimp [G,growthBound];positivity
  have xn : 0≤X := by dsimp [X];positivity
  have m : middleMass T κ L R S ≤ G^k*∑ p∈P,(oneCount T κ p S:ℝ) :=
    middle_card T κ L R S (G^k) (by positivity)
      (fun _ h=>box_weight ((Nat.div_le_self _ _).trans_eq (Nat.sqrt_eq' _)) h)
  have each (p : ℕ) (hp : p∈P) : (oneCount T κ p S:ℝ) ≤
      (C*X/G^k)*(1/(p:ℝ)^2)+E := by
    apply (counts p hp).trans_eq;dsimp [E,G,k,X,N,W];ring
  have M : 0≤C*X/G^k := by positivity
  have ps : P.card≤R := by
    apply (Finset.card_filter_le ..).trans
    simp
  have factor : (G^k)*R= G^(2*k+5) := by
    dsimp [R,logCutoff,G,k];rw [Nat.cast_pow,←pow_add];congr 1;omega
  change D*G^(2*k+5)/(2:ℝ)^t<1/((j:ℝ)+1) at small
  have en : 0≤E := by dsimp [E];positivity
  have total : (∑ p∈P,(oneCount T κ p S:ℝ)) ≤ (C*X/G^k)*((4*Real.log 4)/((L:ℝ)*Real.log L))+(R:ℝ)*E := calc
    _ ≤ _ := sum_le_sum each
    _ = _ := by rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (reciprocal_prime_tail L R two) M)
                        (mul_le_mul_of_nonneg_right (by exact_mod_cast ps) en)
  apply m.trans ((mul_le_mul_of_nonneg_left total (pow_nonneg gn.le k)).trans ?_)
  calc _ = (C*(4*Real.log 4)/Real.log L/(L:ℝ)+D*G^(2*k+5)/(2:ℝ)^t)*X := by
            rw [←factor];dsimp [E]
            have lp : (L:ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
            have logp : Real.log (L:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1<L by omega))).ne'
            field_simp [gn.ne',lp,logp]
       _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add_right small.le _) xn
end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.sharp_transfer
