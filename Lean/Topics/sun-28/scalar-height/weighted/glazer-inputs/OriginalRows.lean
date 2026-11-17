import PellCutoff
import PublishedHeights

namespace ZInQBlueprint.OriginalHeightCount
open scoped Classical
open Finset Height Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
open ZInQ.RouteK
noncomputable section
set_option maxRecDepth 12000
attribute [local irreducible] glazerConstant24

def offMarks (x : ℚ) : Prop := ∀ i, oldForm i x.num x.den ≠ 0

def failure (x : ℚ) : Prop :=
  offMarks x ∧ glazerConstant24*(oddProduct x.num x.den:ℝ)^24 < logHeight₁ x

/-- Strict failure of the literal five-contact estimate on a reduced rational slope. -/
theorem failure_iff_source (x : ℚ) :
    failure x ↔ offMarks x ∧ glazerConstant24*
      (∏ p ∈ oldContactPrimes oldCutoff x.num x.den, (p:ℝ))^24 < pairLogHeight x.num x.den := by
  simp only [failure,oddProduct,primeProduct,oddSupport,Nat.cast_prod,logHeight_reduced_pair]

def signedValue (z : Bool × ℕ × ℕ) : ℚ :=
  ((if z.1 then -(z.2.1:ℤ) else (z.2.1:ℤ)):ℤ)/(z.2.2:ℚ)

def signedPairs (S : Finset ℕ) : Finset ℚ := ((univ : Finset Bool) ×ˢ (S ×ˢ S)).image signedValue

theorem mem_signedPairs (x : ℚ) {S : Finset ℕ} (a : x.num.natAbs∈S) (b : x.den∈S) :
    x∈signedPairs S := by
  by_cases n : 0≤x.num
  · have pos : (x.num.natAbs:ℤ)=x.num := (Int.natCast_natAbs x.num).trans (abs_of_nonneg n)
    refine mem_image.mpr ⟨(false,x.num.natAbs,x.den),mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨a,b⟩⟩,?_⟩
    change (((x.num.natAbs:ℤ):ℚ)/(x.den:ℚ))=x
    rw [pos]
    exact x.num_div_den
  · have neg : -(x.num.natAbs:ℤ)=x.num := by rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge n),neg_neg]
    refine mem_image.mpr ⟨(true,x.num.natAbs,x.den),mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨a,b⟩⟩,?_⟩
    change (((-(x.num.natAbs:ℤ)):ℚ)/(x.den:ℚ))=x
    have negate : -((x.num.natAbs:ℕ):ℚ)=(x.num:ℚ) := by exact_mod_cast neg
    simp only [Int.cast_natCast]
    rw [negate]
    exact x.num_div_den

def exceptions (B : ℕ) : Finset ℚ :=
  (signedPairs (range (B+1))).filter fun x => max x.num.natAbs x.den≤B ∧ failure x

theorem mem_exceptions (x : ℚ) (B : ℕ) :
    x∈exceptions B ↔ max x.num.natAbs x.den≤B ∧ failure x := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · rintro h
    have ab := max_le_iff.mp h.1
    exact mem_filter.mpr ⟨mem_signedPairs x (mem_range.mpr (Nat.lt_succ_of_le ab.1))
      (mem_range.mpr (Nat.lt_succ_of_le ab.2)),h⟩

/-- The root squareclass of each marked row is small at every actual failure. -/
theorem row_square_at_failure {x : ℚ} {B K : ℕ} (atx : x∈exceptions B)
    (threshold : Real.log (B:ℝ) ≤ ((K+1:ℕ):ℝ)^24) (i : Fin 5) :
    ∃ d u : ℕ, 0<d ∧ d≤K ∧ (oldForm i x.num x.den).natAbs=d*u^2 := by
  obtain ⟨box,off,fail⟩ := (mem_exceptions x B).mp atx
  obtain ⟨sf,v,_,eq⟩ := sqfInt_spec (off i)
  let d := (kernel i x.num x.den).natAbs
  have eqn : (oldForm i x.num x.den).natAbs=d*v.natAbs^2 := by
    simpa only [d,kernel,Int.natAbs_mul,Int.natAbs_pow] using congrArg Int.natAbs eq
  have pos : 0<d := Int.natAbs_pos.mpr sf.ne_zero
  have sm := kernel_bound off i
  have hr : (d:ℝ)≤(heightRadical x.num x.den:ℝ) := by exact_mod_cast sm
  have pow := pow_le_pow_left₀ (show 0≤(d:ℝ) by positivity) hr 24
  have lift : (heightRadical x.num x.den:ℝ)^24 ≤ 2^810*(heightRadical x.num x.den:ℝ)^24 := by
    have c : (1:ℝ) ≤ 2^810 := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right c (show 0≤(heightRadical x.num x.den:ℝ)^24 by positivity)
  have small := (pow.trans (lift.trans (original_margin x.num x.den))).trans_lt fail
  rw [Rat.logHeight₁_eq_log_max] at small
  have live : 0 < max x.num.natAbs x.den := x.den_pos.trans_le (le_max_right ..)
  have upper := Real.log_le_log (by exact_mod_cast live : 0<((max x.num.natAbs x.den:ℕ):ℝ))
    (by exact_mod_cast box : ((max x.num.natAbs x.den:ℕ):ℝ)≤(B:ℝ))
  refine ⟨d,v.natAbs,pos,?_,eqn⟩
  by_contra! high
  have g : ((K+1:ℕ):ℝ)≤d := by exact_mod_cast high
  exact (not_le_of_gt ((small.trans_le upper).trans_le threshold)) (pow_le_pow_left₀ (by positivity) g 24)

end
end ZInQBlueprint.OriginalHeightCount
#print axioms ZInQBlueprint.OriginalHeightCount.failure_iff_source
#print axioms ZInQBlueprint.OriginalHeightCount.mem_signedPairs
#print axioms ZInQBlueprint.OriginalHeightCount.mem_exceptions
#print axioms ZInQBlueprint.OriginalHeightCount.row_square_at_failure
