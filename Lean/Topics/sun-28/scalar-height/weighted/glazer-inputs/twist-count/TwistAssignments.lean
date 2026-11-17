import SupportFibres
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Sum the three possible ramification patterns for each prime of the two labels. -/
namespace ZInQBlueprint.TwistCount
open Finset Sun28.FiveDescent ZInQBlueprint.OriginalHeightCount
open scoped Classical
noncomputable section

/-- The weights for a prime in d only, e only, or both equal 7², 7⁴, and 7². -/
def choiceWeight (i : Fin 3) : ℕ := ![49,2401,49] i

abbrev choices (m : ℕ) := (p : m.primeFactors) → Fin 3

def assignmentWeight {m : ℕ} (f : choices m) : ℕ := ∏ p, choiceWeight (f p)

theorem sum_choices (m : ℕ) : (∑ f : choices m, assignmentWeight f) = 2499^omega m := by
  have total : ∑ i : Fin 3, choiceWeight i=2499 := by decide
  unfold assignmentWeight
  rw [←Fintype.prod_sum (fun (_ : m.primeFactors) (i : Fin 3)=>choiceWeight i)]
  simp only [total,prod_const,card_univ,Fintype.card_coe,omega]

def code (m : ℕ) (x : ℚ) : choices m := fun p=>
  if p.1∈(D x.num x.den).natAbs.primeFactors then
    if p.1∈(E x.num x.den).natAbs.primeFactors then 2 else 0 else 1

def signs (x : ℚ) : Bool × Bool :=
  (decide (D x.num x.den < 0),decide (E x.num x.den < 0))

/-- This is the finite geometric certificate. It concerns a single sign and prime
assignment and the sizes of finite sets of slopes, with no height in its hypotheses. -/
def TwistCountCertificate (C : ℝ) : Prop :=
  ∀ (m : ℕ) (s : Bool × Bool) (f : choices m) (X : Finset ℚ),
    (∀ x∈X, offMarks x ∧ label x=m ∧ signs x=s ∧ code m x=f) →
    (X.card:ℝ)≤C*(assignmentWeight f:ℝ)

theorem supportCount_of_certificate {C : ℝ} (cert : TwistCountCertificate C) :
    SupportCount 2499 (4*C) := by
  intro m X valid
  let f (x : ℚ) : (Bool×Bool) × choices m := (signs x,code m x)
  have cnt := card_eq_sum_card_fiberwise (f:=f) (s:=X) (t:=univ) (fun _ _=>mem_univ _)
  have real : (X.card:ℝ)=∑ b : (Bool×Bool) × choices m,
      ((X.filter fun x=>f x=b).card:ℝ) := by exact_mod_cast cnt
  calc
    _ = _ := real
    _ ≤ ∑ b : (Bool×Bool) × choices m, C*(assignmentWeight b.2:ℝ) := by
      apply sum_le_sum
      intro b _
      apply cert m b.1 b.2
      intro x hx
      obtain ⟨ins,eq⟩:=mem_filter.mp hx
      obtain ⟨off,l⟩:=valid x ins
      exact ⟨off,l,congrArg Prod.fst eq,congrArg Prod.snd eq⟩
    _ = (4*C)*(2499:ℝ)^omega m := by
      have ss : (∑ b : choices m, (assignmentWeight b:ℝ))=(2499:ℝ)^omega m := by exact_mod_cast sum_choices m
      rw [Fintype.sum_prod_type]
      simp only [←mul_sum,ss,sum_const,card_univ,Fintype.card_prod,Fintype.card_bool,nsmul_eq_mul]
      push_cast;ring

theorem exceptional_count_of_twists {B K : ℕ} {C : ℝ} (c : 0≤C) (cert : TwistCountCertificate C)
    (threshold : Real.log (B:ℝ)≤((K+1:ℕ):ℝ)^24) :
    ((exceptions B).card:ℝ)≤4*C*(K:ℝ)*(1+Real.log (K:ℝ))^2498 :=
  count_by_support 2498 B K (mul_nonneg (by norm_num) c) (supportCount_of_certificate cert) threshold

end
end ZInQBlueprint.TwistCount
#print axioms ZInQBlueprint.TwistCount.sum_choices
#print axioms ZInQBlueprint.TwistCount.supportCount_of_certificate
#print axioms ZInQBlueprint.TwistCount.exceptional_count_of_twists
