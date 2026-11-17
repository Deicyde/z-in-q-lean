import CutoffEuler
import HeightBudget18

namespace ZInQBlueprint.DiamondHeight
noncomputable section
set_option exponentiation.threshold 320

private theorem euler_sixth (S:Finset ℕ) (prime:∀p∈S,p.Prime) :
    (eulerFactor S)^6≤((∏p∈S,p:ℕ):ℝ)^5 := by
  simp only [Nat.cast_prod,eulerFactor,←Finset.prod_pow]
  apply Finset.prod_le_prod₀ (fun _ _=>by positivity)
  intro p hp
  have pr : (2:ℝ)≤p:=by exact_mod_cast (prime p hp).two_le
  have frac:1/(p:ℝ)≤1/2:=by gcongr
  calc
    _ ≤ (1+1/2:ℝ)^6 := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ (2:ℝ)^5 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) pr _

/-- The last power of the moving character order is saved by the copies of A
in the modular Jacobian. Only one large prime is needed when t exceeds k. -/
theorem character_euler_fifth (S:Finset ℕ) (prime:∀p∈S,p.Prime) (t k:ℕ) (two:2≤k)
    (order:t≤k ∨ ∃p∈S,t≤p-1) :
    (t:ℝ)^5*(eulerFactor S)^6 ≤ (k:ℝ)^5*((∏p∈S,p:ℕ):ℝ)^5 := by
  rcases order with h|⟨p,hp,h⟩
  · exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by exact_mod_cast h) _) (euler_sixth S prime)
      (by positivity) (by positivity)
  · have pp : (2:ℝ)≤p:=by exact_mod_cast (prime p hp).two_le
    have paired : (t:ℝ)*(1+1/(p:ℝ))≤p:= (mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)).trans
      (paired_prime (prime p hp))
    have pos : 0≤(t:ℝ)*(1+1/(p:ℝ)):=by positivity
    have one : 1+1/(p:ℝ) ≤ (k:ℝ)^5 := by
      have frac:1/(p:ℝ)≤1/2:=by gcongr
      have kk : (2:ℝ)≤k:=by exact_mod_cast two
      have raised := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) kk 5
      norm_num at raised
      linarith
    let O:=S.erase p
    have ep : eulerFactor S=(1+1/(p:ℝ))*eulerFactor O := (Finset.mul_prod_erase S _ hp).symm
    have mp : ((∏p∈S,p:ℕ):ℝ)=(p:ℝ)*((∏q∈O,q:ℕ):ℝ) := by
      exact_mod_cast (Finset.mul_prod_erase S (fun q:ℕ=>q) hp).symm
    have eO := euler_sixth O (fun q hq=>prime q (Finset.mem_of_mem_erase hq))
    have eo : 0≤(eulerFactor O)^6:=by positivity
    rw [ep,mp]
    calc
      _ = ((t:ℝ)*(1+1/(p:ℝ)))^5*(1+1/(p:ℝ))*(eulerFactor O)^6 := by ring
      _ ≤ ((p:ℝ)^5*(k:ℝ)^5)*((∏q∈O,q:ℕ):ℝ)^5 :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ pos paired _) one (by positivity) (by positivity))
          eO eo (by positivity)
      _ = _ := by ring

/-- The comparison is for an isogeny with r copies of the surface. A negative
stable height also satisfies the same bound. -/
theorem repeated_surface_height {D d h V:ℝ} (r t:ℕ) (one:1≤V*(t:ℝ)) (dp:1≤d)
    (field:d≤V*(t:ℝ)) (cover:D≤V*(t:ℝ)) (ct:t≤4*r)
    (tp:0<t) (comparison:JacobianComparison D d (r*h)) :
    h≤2^26*V^6*(t:ℝ)^5 := by
  by_cases hp:h≤0
  · exact hp.trans (by positivity)
  have hpos := le_of_lt (lt_of_not_ge hp)
  have base:=jacobian_height one dp field cover comparison
  have bound : (t:ℝ)*h≤4*((r:ℝ)*h) := by
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast ct) hpos
  have tested := bound.trans (mul_le_mul_of_nonneg_left base (by norm_num : (0:ℝ)≤4))
  apply (le_of_mul_le_mul_left _ (by exact_mod_cast tp : 0<(t:ℝ)))
  calc
    _ ≤ _ := tested
    _ = _ := by ring

/-- The manuscript's exponent-17 multiplicity route with the fixed prime
set separated. The hypotheses specify the isogeny over the field of degree d. -/
theorem multiplicity_height17 (S:Finset ℕ) (prime:∀p∈S,p.Prime) (r t k:ℕ) (tp:0<t)
    (two:2≤k) (order:t≤k ∨ ∃p∈S,t≤p-1) (copies:t≤4*r)
    {D d h V0:ℝ} (dp:1≤d)
    (F:JacobianComparison D d (r*h))
    (field:d≤V0*((∏p∈S,p:ℕ):ℝ)^2*eulerFactor S*t)
    (cover:D≤V0*((∏p∈S,p:ℕ):ℝ)^2*eulerFactor S*t) :
    h≤2^26*V0^6*(k:ℝ)^5*((∏p∈S,p:ℕ):ℝ)^17 := by
  let M:ℝ:=((∏p∈S,p:ℕ):ℝ)
  have ht:=repeated_surface_height r t (dp.trans field) dp field cover copies tp F
  have pair:=character_euler_fifth S prime t k two order
  calc
    h ≤ _ := ht
    _ = (2^26*V0^6*M^12)*((t:ℝ)^5*(eulerFactor S)^6) := by dsimp only [M];ring
    _ ≤ (2^26*V0^6*M^12)*((k:ℝ)^5*M^5) := mul_le_mul_of_nonneg_left pair (by positivity)
    _ = _ := by dsimp only [M];ring

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.character_euler_fifth
#print axioms ZInQBlueprint.DiamondHeight.repeated_surface_height

#print axioms ZInQBlueprint.DiamondHeight.multiplicity_height17
