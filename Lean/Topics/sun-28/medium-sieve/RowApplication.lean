import PrimeSummation

namespace Sun28.MediumSieve
open Sun28.SinglePrime Sun28.ContactFactors Sun28.WeightedSelection Finset Filter Topology
open scoped Classical
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

theorem box_weight {t W : ℕ} (w : W≤ side t) {a : Record A d H Y}
    (inside : a∈box (lengthAt t) W) : weight a ≤ (growthBound A t:ℝ)^(shifts A).card := by
  obtain ⟨_,u,v⟩:=box_mem inside
  have vs : W^2≤lengthAt t := Nat.pow_le_pow_left w 2
  have coeff:=Nat.mul_le_mul_left (maxCoefficient A) vs
  have bound : lengthAt t+maxCoefficient A*W^2+1≤envelope A*lengthAt t := by
    dsimp only [envelope];nlinarith only [coeff,show 1≤lengthAt t from Nat.one_le_pow _ _ (side_pos t),Nat.zero_le (maxCoefficient A*lengthAt t)]
  apply (weight_bound a u v).trans
  apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 _))
  apply (small_log _ t _ bound).2.trans
  dsimp [growthBound];exact_mod_cast Nat.le_succ _

theorem one_prime_transfer {T : Finset ℕ} {κ L J : ℕ} {C : ℝ} (positive : 0<L)
    (cn : 0≤C) (count : PrimeRow A d H Y T κ L J C) : LogRow A d H Y T κ L J C := by
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
  have total : (∑ p∈P,(oneCount T κ p S:ℝ)) ≤ (C*X/G^k)*(1/(L:ℝ))+(R:ℝ)*E := calc
    _ ≤ _ := sum_le_sum each
    _ = _ := by rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (reciprocal_squares L R positive) M)
                        (mul_le_mul_of_nonneg_right (by exact_mod_cast ps) en)
  apply m.trans ((mul_le_mul_of_nonneg_left total (pow_nonneg gn.le k)).trans ?_)
  calc _ = (C/(L:ℝ)+D*G^(2*k+5)/(2:ℝ)^t)*X := by
            rw [←factor];dsimp [E];field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add_right small.le _) xn
end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.box_weight
#print axioms Sun28.MediumSieve.one_prime_transfer
