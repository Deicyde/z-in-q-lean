import BalancedSector

/-! A single squareclass match removes one of the three rational conductor rows. -/
namespace Sun28.HeightBalance
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.MinimalConductors Height
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.HeightFibres Sun28.HeightFibres.Sharp
open private factors form_diff from BalancedUnits
open private int_height from ContactHeight
noncomputable section

structure ThreeRows where
  center : Fin 5
  a : Fin 5
  b : Fin 5
  ia : center ≠ a
  ib : center ≠ b
  ab : a ≠ b

namespace ThreeRows
structure Match (R : ThreeRows) (A B d u v : ℤ) : Prop where
  first : det R.center R.b * oldForm R.a A B=d*u^2
  second : det R.center R.a * oldForm R.b A B=d*v^2

def primes (R : ThreeRows) (A B : ℤ) := (core ∪ formPrimes R.center A B) ∪ formPrimes R.a A B
def coordinate (u v : ℤ) : ℚ := ((u+v:ℤ):ℚ)/((2*u:ℤ):ℚ)

theorem equation (R : ThreeRows) {A B d u v : ℤ} (off : ∀ i,oldForm i A B≠0) (h:R.Match A B d u v) :
    RationalSUnit (R.primes A B) (coordinate u v) ∧ RationalSUnit (R.primes A B) (1-coordinate u v) ∧
    crossRatio R.a R.b R.center A B = (4*coordinate u v*(1-coordinate u v))⁻¹ := by
  let S:=R.primes A B
  have minor : det R.center R.b≠0:=det_ne R.ib
  have first := h.first
  have second := h.second
  have cd : core⊆S:=Finset.subset_union_left.trans Finset.subset_union_left
  have nz : u≠0:=fun z=>mul_ne_zero minor (off R.a) (by simp [first,z])
  have difference : d*(u^2-v^2)=det R.a R.b*oldForm R.center A B := by
    linear_combination -first + second + form_diff R.center R.a R.b A B
  have ⟨sp,sm⟩:=factors (det_ne R.ab) (off _) difference ((minor_support _ _).trans cd)
    (Finset.subset_union_right.trans Finset.subset_union_left : (oldForm R.center A B).natAbs.primeFactors ⊆ S)
  have du : u∣det R.center R.b*oldForm R.a A B:=⟨d*u,by rw [first];ring⟩
  have sub : u.natAbs.primeFactors⊆S:=by
    apply (Nat.primeFactors_mono (Int.natAbs_dvd_natAbs.mpr du)
      (Int.natAbs_ne_zero.mpr (mul_ne_zero minor (off R.a)))).trans
    rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr minor) (Int.natAbs_ne_zero.mpr (off R.a))]
    exact Finset.union_subset ((minor_support _ _).trans cd) Finset.subset_union_right
  have supp : (2*u).natAbs.primeFactors⊆S:=by
    rw [Int.natAbs_mul,Nat.primeFactors_mul (by decide) (Int.natAbs_ne_zero.mpr nz)]
    have two : (2:ℤ).natAbs.primeFactors⊆core :=
      Nat.primeFactors_mono (by decide : 2∣210) (by decide)
    exact Finset.union_subset (two.trans cd) sub
  have den : 2*u≠0:=mul_ne_zero (by decide) nz
  have dc : ((2*u:ℤ):ℚ)≠0:=by exact_mod_cast den
  have complement : 1-coordinate u v=((u-v:ℤ):ℚ)/((2*u:ℤ):ℚ):=by
    unfold coordinate;field_simp [dc];push_cast;ring
  refine ⟨ratio_unit sp.1 den sp.2 supp, complement ▸ ratio_unit sm.1 den sm.2 supp,?_⟩
  have eq : (det R.center R.b*oldForm R.a A B)*(u^2-v^2)=(det R.a R.b*oldForm R.center A B)*u^2:=by
    linear_combination (u^2-v^2)*first + u^2*difference
  have qn : (u:ℚ)≠0:=by exact_mod_cast nz
  have q₁ : (u:ℚ)+(v:ℚ)≠0:=by exact_mod_cast sp.1
  have q₂ : (u:ℚ)-(v:ℚ)≠0:=by exact_mod_cast sm.1
  have diff : u^2-v^2≠0:=by
    rw [sq_sub_sq]
    exact mul_ne_zero sp.1 sm.1
  have rep : crossRatio R.a R.b R.center A B=(u:ℚ)^2/((u:ℚ)^2-(v:ℚ)^2) := by
    unfold crossRatio
    apply (div_eq_div_iff (by exact_mod_cast mul_ne_zero (det_ne R.ab) (off R.center))
      (by exact_mod_cast diff)).mpr
    exact_mod_cast (eq.trans (mul_comm _ _))
  rw [rep,complement]
  unfold coordinate
  push_cast
  field_simp [q₁,q₂,qn,show (u:ℚ)^2-(v:ℚ)^2≠0 by exact_mod_cast diff]
  ring

theorem height (units:PublishedCorollary72) (R : ThreeRows) {A B d u v : ℤ}
    (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0) (h:R.Match A B d u v) :
    pairLogHeight A B≤2*FourRows.heightBound (primeProduct (R.primes A B))+34 := by
  obtain ⟨hu,hv,cr⟩:=R.equation off h
  have ps (p:ℕ) (hp:p∈R.primes A B):p.Prime:=by
    rcases Finset.mem_union.mp hp with left|right
    · rcases Finset.mem_union.mp left with a|b <;> exact Nat.prime_of_mem_primeFactors ‹_›
    · exact Nat.prime_of_mem_primeFactors right
  let x:=coordinate u v
  let H:=FourRows.heightBound (primeProduct (R.primes A B))
  have bounds:=supported_corollary units _ ps x (1-x) hu hv (by ring)
  have bh : logHeight₁ x≤H ∧ logHeight₁ (1-x)≤H := by
    simpa only [H,FourRows.heightBound,show (2:ℝ)^7=128 by norm_num] using bounds
  have loss:=crossRatio_height R.a R.b R.center R.ab R.ia.symm R.ib.symm cop off
  rw [cr,logHeight₁_inv] at loss
  have h₁:=logHeight₁_mul_le (4:ℚ) x
  have h₂:=logHeight₁_mul_le (4*x) (1-x)
  have h₄ : logHeight₁ (4:ℚ)≤2 := by
    rw [Rat.logHeight₁_eq_log_max];norm_num
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow];norm_num
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  change pairLogHeight A B≤logHeight₁ (4*x*(1-x))+32 at loss
  change pairLogHeight A B≤2*H+34
  linarith only [loss,h₁,h₂,h₄,bh.1,bh.2]

end ThreeRows

def PairCovered (A B:ℤ) : Prop :=
  ∃ (R:ThreeRows) (d u v:ℤ), R.Match A B d u v ∧ primeProduct (R.primes A B)≤heightRadical A B^23

theorem five_height_of_pair (units:PublishedCorollary72) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (cover:PairCovered A B) : target A B := by
  obtain ⟨R,d,u,v,h,small⟩:=cover
  let T:ℝ:=heightRadical A B
  let N:=primeProduct (R.primes A B)
  have one:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have pr (p : ℕ) (hp:p∈R.primes A B) : p.Prime:=by
    rcases Finset.mem_union.mp hp with L|a
    · rcases Finset.mem_union.mp L with a|a <;> exact Nat.prime_of_mem_primeFactors a
    · exact Nat.prime_of_mem_primeFactors a
  have np:1≤(N:ℝ):=Nat.one_le_cast.mpr (Finset.prod_pos (fun _ hp=>(pr _ hp).pos))
  have absorb:=analytic_absorption np one (show (N:ℝ)≤T^23 by dsimp only [N,T];exact_mod_cast small)
  change FourRows.heightBound N≤(192*53^2)*T^24+65 at absorb
  have h₀:=R.height units cop off h
  change pairLogHeight A B≤2*FourRows.heightBound N+34 at h₀
  have hh:pairLogHeight A B≤2^21*T^24:=by linarith only [h₀,absorb,one_le_pow₀ one (n:=24)]
  have slack:2^21*T^24≤2^810*T^24:=mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 21≤810)) (by positivity)
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using (hh.trans slack).trans (original_margin A B)

/-- The remaining slopes fail every earlier chart, all one-row charts, and all two-row charts. -/
def Remaining : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) → glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬HeightRefinement.Sharp.Test i A B b c) → ¬Covered A B → ¬PairCovered A B → target A B

theorem original_iff_pairs (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ Remaining := by
  constructor
  · exact fun full A B cop off _ _ _ _ _=>full A B cop off
  · intro rem
    apply (original_iff_balance units pell classes formula).mpr
    intro A B cop off s l f c
    by_cases p:PairCovered A B
    · exact five_height_of_pair units cop off p
    · exact rem A B cop off s l f c p

end
end Sun28.HeightBalance
#print axioms Sun28.HeightBalance.ThreeRows.equation
#print axioms Sun28.HeightBalance.ThreeRows.height
#print axioms Sun28.HeightBalance.five_height_of_pair
#print axioms Sun28.HeightBalance.original_iff_pairs
