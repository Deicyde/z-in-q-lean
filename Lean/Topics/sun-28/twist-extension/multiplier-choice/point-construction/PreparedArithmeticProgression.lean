import PreparedProgressionBase

namespace Sun28.PointConstruction
open Sun28.Ordinary Sun28.ScalarHeight Sun28.TwistRank Sun28.FixedPreparation Sun28.FinitePole
  Sun28.ContactFactors Sun28.PreparedPoles
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

private theorem progression_depth (n p:ℕ) (mem:p∈primes) : 4≤padicValRat p (inputB (progression n)) := by
  obtain ⟨large,comp⟩:=denominator_facts n
  have cpos : 0<(gamma:ℚ) := by exact_mod_cast gamma_positive
  have ln : 2*(scalarCoefficient:ℚ)*gamma < (progressionDen n:ℚ) := by exact_mod_cast large
  have js : 0<(progressionDen n:ℚ) := lt_trans (mul_pos (mul_pos (by norm_num) (by norm_num [scalarCoefficient])) cpos) ln
  have value : inputB (progression n) = (scalarCoefficient:ℚ)*((gamma:ℚ)/(progressionDen n:ℚ))^2 := rfl
  have pp : p.Prime := (show ∀ p∈primes,p.Prime by decide) p mem
  let _ : Fact p.Prime:=⟨pp⟩
  have dp : p∣FixedPreparation.primorial := prime_product ▸ Finset.dvd_prod_of_mem (fun k:ℕ=>k) mem
  have pv : p∣scalarCoefficient*gamma := dvd_mul_of_dvd_right (dvd_pow dp two_ne_zero) scalarCoefficient
  have nod : ¬p∣(progressionDen n).natAbs := by
    intro bad
    exact pp.not_dvd_one (comp ▸ Nat.dvd_gcd pv bad)
  have unit : padicValRat p ((progressionDen n:ℤ):ℚ)=0 := by
    rw [padicValRat.of_int]; change ((padicValNat p (progressionDen n).natAbs:ℕ):ℤ)=0
    rw [padicValNat.eq_zero_of_not_dvd nod];rfl
  have cf : (scalarCoefficient:ℚ)≠0:=by norm_num [scalarCoefficient]
  rw [value,padicValRat.mul cf (pow_ne_zero 2 (div_ne_zero cpos.ne' js.ne')),
    padicValRat.pow,padicValRat.div cpos.ne' js.ne',fixed_gamma_order p mem,unit]
  have nonneg := zero_le_padicValRat_of_nat (p:=p) scalarCoefficient
  omega

theorem progression_prepared (n:ℕ) : ClassPrepared (inputB (progression n)) := by
  obtain ⟨dsq,bp,small⟩:=interval_den n
  obtain ⟨large,_⟩:=denominator_facts n
  have cpos : 0<(gamma:ℚ) := by exact_mod_cast gamma_positive
  have ln : 2*(scalarCoefficient:ℚ)*gamma < (progressionDen n:ℚ) := by exact_mod_cast large
  have js : 0<(progressionDen n:ℚ) := lt_trans (mul_pos (mul_pos (by norm_num) (by norm_num [scalarCoefficient])) cpos) ln
  have rad : scalarRadicand (beta 0) = -31581660 := by norm_num [beta,scalarRadicand]
  let w : ℚ := (1+(denominator:ℚ)*31581660^2)/(2*(progressionDen n:ℚ))
  have normB : signedValue (scalarRadicand (beta 0)) (-1) gamma denominator w = inputB (progression n) := by
    rw [rad]; dsimp [signedValue,w,inputB,progression]
    have nz : (1:ℚ)+(denominator:ℚ)*31581660^2≠0 := by positivity
    field_simp [js.ne',nz];ring
  refine ⟨⟨dsq,bp,small,progression_depth n⟩,?_⟩
  intro m b t mem c
  rw [←normB] at c bp
  have r:(-1:ℚ)*scalarRadicand (beta ((0:ℤ):ℚ))=((integerRadicand 0).natAbs:ℚ) := by
    norm_num [integerRadicand,scalarRadicand,beta]
  obtain ⟨p,q⟩:=scalar_class (X:=0) c bp r
  exact Or.inr ⟨0,m,p,mem,q⟩
end
end Sun28.PointConstruction
#print axioms Sun28.PointConstruction.progression_prepared
