import MarkedConductor

namespace Sun28.HeightCubics.Refinement
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.MinimalConductors
noncomputable section

/-- The logarithms cost one power of the full radical. -/
theorem absorb_cap {n t:ℕ} (np:0<n) (tp:0<t) (nb:n≤62208*t^23) :
    heightBound n≤(2:ℝ)^31*(t:ℝ)^24 := by
  let T:ℝ:=t
  have one:1≤T:=Nat.one_le_cast.mpr tp
  have zero:0<T:=lt_of_lt_of_le zero_lt_one one
  have so:1≤Real.sqrt T:=by simpa using Real.sqrt_le_sqrt one
  have sq:Real.sqrt T^2=T:=Real.sq_sqrt zero.le
  have gl:Real.log T≤2*Real.sqrt T:=by
    have e:=Real.log_pow (Real.sqrt T) 2
    rw [sq] at e
    norm_num at e
    linarith only [e,Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr zero)]
  have n1:1≤(n:ℝ):=Nat.one_le_cast.mpr np
  have upper:(n:ℝ)≤62208*T^23:=by dsimp [T];exact_mod_cast nb
  have l:=Real.log_le_log (lt_of_lt_of_le zero_lt_one n1) upper
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ zero.ne'),Real.log_pow] at l
  have c:=Real.log_le_log (by norm_num:(0:ℝ)<62208) (show (62208:ℝ)≤2^16 by norm_num)
  rw [Real.log_pow] at c
  have lg:Real.log (n:ℝ)≤62*Real.sqrt T:=by
    push_cast at c l
    linarith only [gl,l,c,so,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]
  have sqle:=pow_le_pow_left₀ (Real.log_nonneg n1) lg 2
  rw [mul_pow,sq] at sqle
  have m:=mul_le_mul upper sqle (sq_nonneg _) (by positivity)
  change (9/2)*(n:ℝ)*(Real.log (n:ℝ))^2+281≤(2:ℝ)^31*T^24
  nlinarith only [m,one_le_pow₀ one (n:=24)]

def Covered (A B:ℤ) : Prop :=
  ∃ r:ThreeRows,heightBound (conductorCap r A B)≤glazerConstant24*(oddProduct A B:ℝ)^24

theorem five_height_of_conductor (pub:PublishedElliptic) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (covered:Covered A B) : target A B := by
  obtain ⟨r,cap⟩:=covered
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using (marked_height pub r cop off).trans cap

theorem pair_covered {A B:ℤ} (i j:Fin 5) (ij:i≠j)
    (budget:hidden i A B*noncubic j A B^2≤heightRadical A B^21) : Covered A B := by
  have pick:∀ i j:Fin 5,i≠j → ∃ k:Fin 5,i≠k ∧ k≠j:=by decide
  obtain ⟨k,ik,kj⟩:=pick i j ij
  let r:ThreeRows:=⟨i,k,j,ik,ij,kj⟩
  let T:=heightRadical A B
  have tpos:0<T:=Nat.mul_pos pos_cutoff (pos_odd _ _)
  have dp:0<hidden i A B:=Nat.pos_of_ne_zero (prime_product_nonzero _
    (fun p mem=>Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp mem).1))
  have up:0<noncubic j A B:=Nat.pos_of_ne_zero (prime_product_nonzero _
    (fun p mem=>Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp (Finset.mem_filter.mp mem).1).1))
  have cap:conductorCap r A B=62208*T^2*(hidden i A B*noncubic j A B^2):=by
    change 62208*T^2*noncubic j A B^2*hidden i A B=_;ring
  have small:conductorCap r A B≤62208*T^23:=by
    rw [cap]
    exact (Nat.mul_le_mul_left _ budget).trans_eq (by change 62208*T^2*T^21=_;ring)
  have live:0<conductorCap r A B:=by rw [cap];positivity
  have cmp:=absorb_cap live tpos small
  have margin: (2:ℝ)^31≤2^810:=pow_le_pow_right₀ (by norm_num) (by decide)
  exact ⟨r,(cmp.trans (mul_le_mul_of_nonneg_right margin (by positivity))).trans (original_margin A B)⟩

end
end Sun28.HeightCubics.Refinement
#print axioms Sun28.HeightCubics.Refinement.absorb_cap
#print axioms Sun28.HeightCubics.Refinement.five_height_of_conductor
#print axioms Sun28.HeightCubics.Refinement.pair_covered
