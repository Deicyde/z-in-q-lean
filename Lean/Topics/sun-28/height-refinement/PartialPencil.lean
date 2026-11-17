import BudgetSector

namespace Sun28.HeightRefinement
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres Sun28.HeightFibres.Sharp
  Sun28.HeightExtension Height ZInQ.RouteK
open private leftRow midRow rightRow mult catalogue delta₁ delta₂ equation_rows linear_log from FivePencils
open private numberLog_le from PellSectors
open private int_height height_div det_log from ContactHeight
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 160

def primeBase (b : ℤ) := primeProduct b.natAbs.primeFactors

private theorem fraction_support (a b : ℤ) (nb:b≠0) :
    (((a:ℚ)/(b:ℚ)).den).primeFactors⊆b.natAbs.primeFactors := by
  have div : ((((a:ℚ)/(b:ℚ)).den:ℕ):ℤ)∣b := by
    simpa only [←Rat.divInt_eq_div] using Rat.den_dvd a b
  exact Nat.primeFactors_mono (Int.natAbs_dvd_natAbs.mpr div) (Int.natAbs_ne_zero.mpr nb)

/-- Strip an arbitrary square divisor from one row. Only its own primes
are inverted; the complementary integer appears linearly in the right sides. -/
theorem partial_pencil {A B b c : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5)
    (split : oldForm i A B=b^2*c) :
    ∃ (g h k I J : ℤ) (x y z : ℚ),
      g≠0 ∧ h≠0 ∧ k≠0 ∧ I≠0 ∧ J≠0 ∧ I≠J ∧
      g.natAbs.primeFactors⊆support A B ∧ h.natAbs.primeFactors⊆support A B ∧ k.natAbs.primeFactors⊆support A B ∧
      (∀ a∈([g,h,k]:List ℤ),a.natAbs≤2^32*heightRadical A B) ∧
      numberLog I≤numberLog c+32 ∧ numberLog J≤numberLog c+32 ∧
      x.den.primeFactors⊆b.natAbs.primeFactors ∧ y.den.primeFactors⊆b.natAbs.primeFactors ∧ z.den.primeFactors⊆b.natAbs.primeFactors ∧
      (g:ℚ)*x^2-(h:ℚ)*y^2=(I:ℚ) ∧ (g:ℚ)*x^2-(k:ℚ)*z^2=(J:ℚ) ∧
      (oldForm (leftRow i) A B:ℚ)/(oldForm i A B:ℚ)=(kernel (leftRow i) A B:ℚ)/(c:ℚ)*x^2 := by
  have live := off i
  have bn:b≠0:=fun z=>live (by simp [split,z])
  have cn:c≠0:=fun z=>live (by simp [split,z])
  let l:=leftRow i; let m:=midRow i; let n:=rightRow i
  obtain ⟨_,u,_,fu⟩:=sqfInt_spec (off l)
  obtain ⟨_,v,_,fv⟩:=sqfInt_spec (off m)
  obtain ⟨_,w,_,fw⟩:=sqfInt_spec (off n)
  change oldForm l A B=kernel l A B*u^2 at fu
  change oldForm m A B=kernel m A B*v^2 at fv
  change oldForm n A B=kernel n A B*w^2 at fw
  obtain ⟨mu,nd,ne,de,bd,be⟩:=catalogue i
  let G (j:Fin 3) (r:Fin 5):=mult i j*kernel r A B
  have nz (j r) : G j r≠0:=mul_ne_zero (mu j).1 (sqfInt_spec (off r)).1.ne_zero
  have cap (j r) : (G j r).natAbs≤2^32*heightRadical A B := by
    dsimp only [G];rw [Int.natAbs_mul];exact Nat.mul_le_mul (mu j).2 (kernel_bound off r)
  obtain ⟨e₁,e₂⟩:=equation_rows i A B
  change mult i 0*oldForm l A B-mult i 1*oldForm m A B=delta₁ i*oldForm i A B at e₁
  change mult i 0*oldForm l A B-mult i 2*oldForm n A B=delta₂ i*oldForm i A B at e₂
  rw [fu,fv,split] at e₁;rw [fu,fw,split] at e₂
  have qb:(b:ℚ)≠0:=by exact_mod_cast bn
  have qc:(c:ℚ)≠0:=by exact_mod_cast cn
  have ce₁:=congrArg (fun u:ℤ=>(u:ℚ)) e₁;have ce₂:=congrArg (fun u:ℤ=>(u:ℚ)) e₂
  push_cast at ce₁ ce₂
  refine ⟨G 0 l,G 1 m,G 2 n,delta₁ i*c,delta₂ i*c,(u:ℚ)/b,(v:ℚ)/b,(w:ℚ)/b,
    nz 0 l,nz 1 m,nz 2 n,mul_ne_zero nd cn,mul_ne_zero ne cn,fun e=>de (mul_right_cancel₀ cn e),
    scaled_support off i 0 l,scaled_support off i 1 m,scaled_support off i 2 n,?_,
    linear_log nd cn bd,linear_log ne cn be,fraction_support _ _ bn,fraction_support _ _ bn,
    fraction_support _ _ bn,?_,?_,?_⟩
  · intro a ha;simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl;exacts [cap 0 l,cap 1 m,cap 2 n]
  · dsimp [G];push_cast;field_simp;linear_combination ce₁
  · dsimp [G];push_cast;field_simp;linear_combination ce₂
  · change (oldForm l A B:ℚ)/_=_;rw [fu,split];push_cast;field_simp;ring

open Sun28.FiveMarkTriples
/-- The cost of recovering the slope includes only one copy of the height
of the complementary integer. -/
theorem partial_recovery {A B c : ℤ} (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0)
    (i : Fin 5) (x:ℚ) (nz:c≠0)
    (ratio : (oldForm (leftRow i) A B:ℚ)/(oldForm i A B:ℚ)=(kernel (leftRow i) A B:ℚ)/(c:ℚ)*x^2) :
    pairLogHeight A B≤2*logHeight₁ x+Real.log (heightRadical A B:ℝ)+numberLog c+96 := by
  let l:=leftRow i;let j:=midRow i
  have cat : ∀ i:Fin 5,leftRow i≠midRow i ∧ leftRow i≠i ∧ midRow i≠i:=by decide
  have ⟨lj,li,ji⟩:=cat i
  have base:=Sun28.FiveMarkTriples.crossRatio_height l j i lj li ji cop off
  have nu : kernel l A B≠0:=(sqfInt_spec (off l)).1.ne_zero
  have coeff:logHeight₁ ((kernel l A B:ℤ):ℚ)≤Real.log (heightRadical A B:ℝ):=by
    rw [int_height nu];exact numberLog_le nu (Nat.cast_le.mpr (kernel_bound off l))
  let α:ℚ:=(det i j:ℚ)/(det l j:ℚ)
  let β:ℚ:=(kernel l A B:ℚ)/(c:ℚ)
  have frac : crossRatio l j i A B=α*(β*x^2) := by
    change (oldForm l A B:ℚ)/(oldForm i A B:ℚ)=β*x^2 at ratio
    rw [←ratio];unfold crossRatio α;push_cast;ring
  have den:=height_div (det i j:ℚ) (det l j:ℚ)
  have dd:=height_div (kernel l A B:ℚ) (c:ℚ)
  change logHeight₁ α≤_ at den
  change logHeight₁ β≤_ at dd
  rw [int_height nz] at dd
  have qr:=logHeight₁_mul_le α (β*x^2)
  have xx:=logHeight₁_mul_le β (x^2)
  rw [logHeight₁_pow] at xx
  rw [frac] at base;norm_num at xx
  linarith only [base,qr,xx,den,dd,coeff,det_log ji.symm,det_log lj]

end
end Sun28.HeightRefinement
#print axioms Sun28.HeightRefinement.partial_pencil
#print axioms Sun28.HeightRefinement.partial_recovery
