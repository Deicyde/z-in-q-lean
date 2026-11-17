import SignedSupport

/-! Exact height reduction, including the original constant and cutoff, in both directions. -/
namespace Sun28.FiveDescent
open Sun28.Ordinary Sun28.FiveMarkUnits Height
noncomputable section

def TwistHeight (H : ℝ) : Prop :=
  ∀ (d e : ℤ), Squarefree d → Squarefree e → ∀ x y : ℚ, x≠0 → y≠0 →
    (e:ℚ)*y^2=sextic d x →
    logHeight₁ (parameter d x)≤H*(primeProduct (twistPrimes d e):ℝ)^24

/-- The conclusion uses the literal rational slope height. Thus passing to the
degree-four genus-two cover loses no additive term or multiplicative constant. -/
theorem original_iff_twist (H : ℝ) : OriginalFiveHeight H oldCutoff ↔ TwistHeight H := by
  constructor
  · intro main d e sd se x y nx ny point
    let s:=parameter d x
    obtain ⟨off,hd,he⟩:=inverse sd se nx ny point
    have cop : Int.gcd s.num (s.den:ℤ)=1 := by simpa [Int.gcd] using s.reduced.gcd_eq_one
    have nb : (s.den:ℤ)≠0 := by exact_mod_cast s.den_nz
    have cmp := signed_height nb cop
    change logHeight₁ ((s.num:ℚ)/(s.den:ℚ))=pairLogHeight s.num s.den at cmp
    rw [Rat.num_div_den] at cmp
    change (∀ i,oldForm i s.num s.den≠0) at off
    change D s.num s.den=d at hd
    change E s.num s.den=e at he
    have out := main _ _ cop off
    rw [support_exact cop off,hd,he,←cmp] at out
    simpa only [primeProduct,Nat.cast_prod,s] using out
  · intro main A B cop off
    obtain ⟨sd,se,x,y,nx,ny,pt,slope⟩:=forward off
    have out:=main _ _ sd se x y nx ny pt
    rw [slope,signed_height (rows off).2.1 cop] at out
    rw [support_exact cop off]
    simpa only [primeProduct,Nat.cast_prod] using out

theorem glazer_iff_twist :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ TwistHeight glazerConstant24 :=
  original_iff_twist _

/-- The usual abscissa height differs from half the recovered slope height by
at most (h(d)+log 2)/2. This comparison is valid in both directions. -/
theorem height_comparison {d : ℤ} (nd : d≠0) (x : ℚ) :
    |logHeight₁ (parameter d x)-2*logHeight₁ x|≤logHeight₁ (d:ℚ)+Real.log 2 := by
  let a:ℚ:=d
  have an : a≠0 := by dsimp [a];exact_mod_cast nd
  let t:=a*x^2
  have coeff : (totalWeight ℚ:ℝ)=1 := by rw [NumberField.totalWeight_eq_finrank];simp
  have left:=logHeight₁_sub_le (1:ℚ) t
  have right:=logHeight₁_sub_le (1:ℚ) (1-t)
  rw [show (1:ℚ)-(1-t)=t by ring] at right
  rw [coeff,one_mul,logHeight₁_one,add_zero] at left right
  have L:=logHeight₁_mul_le a (x^2)
  have R:=logHeight₁_mul_le a⁻¹ t
  have eq : a⁻¹*t=x^2 := by dsimp [t];field_simp
  rw [eq,logHeight₁_inv,logHeight₁_pow] at R
  rw [logHeight₁_pow] at L
  change logHeight₁ t≤_ at L
  change |logHeight₁ ((1-t)⁻¹)-2*logHeight₁ x|≤logHeight₁ a+Real.log 2
  rw [logHeight₁_inv,abs_le]
  norm_num at L R
  constructor <;> linarith

/-- A conventional abscissa estimate, with the signed coefficient height and
the single factor of 2 displayed, suffices for the paper's exact coefficient. -/
theorem original_of_abscissae (H : ℝ)
    (bound : ∀ (d e : ℤ), Squarefree d → Squarefree e → ∀ x y : ℚ, x≠0 → y≠0 →
      (e:ℚ)*y^2=sextic d x →
      2*logHeight₁ x+logHeight₁ (d:ℚ)+Real.log 2≤H*(primeProduct (twistPrimes d e):ℝ)^24) :
    OriginalFiveHeight H oldCutoff := by
  apply (original_iff_twist H).mpr
  intro d e sd se x y nx ny pt
  have h:=(abs_le.mp (height_comparison sd.ne_zero x)).2
  linarith only [h,bound d e sd se x y nx ny pt]

/-- A bound for the full union of the two coefficient supports spends the
fixed primorial only once. The coefficient agrees with the one in Glazer's formula. -/
theorem glazer_of_full_support
    (bound : ∀ (d e : ℤ), Squarefree d → Squarefree e → ∀ x y : ℚ, x≠0 → y≠0 →
      (e:ℚ)*y^2=sextic d x →
      logHeight₁ (parameter d x) ≤
        2*((4608:ℝ)^165888+6^100)*(primeProduct (parameterPrimes d e):ℝ)^24+128) :
    OriginalFiveHeight glazerConstant24 oldCutoff := by
  apply glazer_iff_twist.mpr
  intro d e sd se x y nx ny pt
  let O:=primeProduct (twistPrimes d e)
  let C:=cutoffProduct
  let K:ℝ:=2*((4608:ℝ)^165888+6^100)
  have oo : 0<O := Finset.prod_pos fun p hp=>by
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hp).1 with h|h <;>
      exact (Nat.prime_of_mem_primeFactors h).pos
  have o : (1:ℝ)≤(O:ℝ) := by exact_mod_cast oo
  have compare : (primeProduct (parameterPrimes d e):ℝ)≤(C:ℝ)*O := by
    exact_mod_cast fixed_cost d e
  have power:=pow_le_pow_left₀ (Nat.cast_nonneg _) compare 24
  rw [mul_pow] at power
  have ko : 0≤K := by dsimp [K];positivity
  have ones : (1:ℝ)≤(O:ℝ)^24 := one_le_pow₀ o
  have result:=bound d e sd se x y nx ny pt
  have hmin : (128:ℝ)≤128*(O:ℝ)^24 := by linarith only [ones]
  change logHeight₁ (parameter d x) ≤ glazerConstant24*(O:ℝ)^24
  have unfoldH : glazerConstant24=K*(C:ℝ)^24+128 := by
    simp only [glazerConstant24,K,C,cutoffProduct,primeProduct,Nat.cast_prod]
  rw [unfoldH,add_mul,mul_assoc]
  exact result.trans (add_le_add (mul_le_mul_of_nonneg_left power ko) hmin)


end
end Sun28.FiveDescent
#print axioms Sun28.FiveDescent.original_iff_twist
#print axioms Sun28.FiveDescent.glazer_iff_twist
#print axioms Sun28.FiveDescent.height_comparison
#print axioms Sun28.FiveDescent.original_of_abscissae

#print axioms Sun28.FiveDescent.glazer_of_full_support
