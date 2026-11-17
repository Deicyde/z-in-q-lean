import TYZTraceAction
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! Dirichlet convolution over the two-element field on squarefree inputs. -/
namespace ZInQBlueprint.TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq
abbrev AF := ArithmeticFunction (ZMod 2)

/-- Swapping the two factors cancels all terms off the diagonal. On squarefree inputs
only 1 can have a diagonal pair. -/
theorem square_on_squarefree (f : AF) (h1 : f 1 = 1) {n : ℕ} (hs : Squarefree n) :
    (f*f) n = (1 : AF) n := by
  by_cases hn : n = 1
  · simp [hn,h1]
  rw [ArithmeticFunction.one_apply_ne hn,ArithmeticFunction.mul_apply]
  apply Finset.sum_involution (fun p _ => p.swap)
  · rintro ⟨a,b⟩ _
    change f a * f b + f b * f a = 0
    rw [mul_comm (f b) (f a),←two_mul]
    rw [show (2 : ZMod 2) = 0 by decide,zero_mul]
  · rintro ⟨a,b⟩ hp _ he
    have hab : b = a := congrArg Prod.fst he
    subst b
    have hmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hu : IsUnit a := hs a (dvd_of_eq hmul)
    have ha := Nat.isUnit_iff.mp hu
    exact hn (by simpa [ha] using hmul.symm)
  · exact fun _ _ => rfl
  · exact fun p hp => Nat.swap_mem_divisorsAntidiagonal.mpr hp

private abbrev small (n : ℕ) : Prop := n%8=1 ∨ n%8=3
private abbrev large (n : ℕ) : Prop := n%8=5 ∨ n%8=7

private def kernel (L : ℕ → ℤ) : AF := ⟨fun n => if small n then (L n : ZMod 2) else 0, by simp [small]⟩
private def row (L : ℕ → ℤ) : AF := ⟨fun n => if large n then (traceCoefficient L n : ZMod 2) else 0, by simp [large]⟩
private def seven : AF := ⟨fun n => if n%8=7 then (genusNumber n : ZMod 2) else 0, by decide⟩

private theorem factors_filter {n : ℕ} (hn : large n) :
    (n.divisors.erase 1).filter (fun t => small t ∧ large (n/t)) = recursionFactors n := by
  ext t
  simp only [Finset.mem_filter,Finset.mem_erase,recursionFactors,small,large]
  constructor
  · rintro ⟨⟨hne,ht⟩,hts,htl⟩
    have ht0 := Nat.pos_of_mem_divisors ht
    exact ⟨ht,by omega,by tauto,by tauto⟩
  · rintro ⟨ht,hgt,hres,hco⟩
    have ht2 : t%8 ≠ 2 := by
      intro h
      have hdiv : 2 ∣ t := Nat.dvd_of_mod_eq_zero (by omega)
      have := hdiv.trans (Nat.mem_divisors.mp ht).1
      rcases hn with h|h <;> omega
    have hco' := cofactor_odd_class (Finset.mem_filter.mpr ⟨ht,hgt,hres,hco⟩) hn
    exact ⟨⟨by omega,ht⟩,by tauto,hco'⟩

private theorem large_of_factors {n t : ℕ} (ht : t ∣ n) (h1 : small t) (h2 : large (n/t)) : large n := by
  have e : ((n/t)%8*(t%8))%8 = n%8 := (Nat.mul_mod _ _ _).symm.trans (congrArg (·%8) (Nat.div_mul_cancel ht))
  rcases h1 with h|h <;> rcases h2 with k|k <;> rw [h,k] at e <;> norm_num at e <;> unfold large <;> omega

private theorem small_of_complement {n e : ℕ} (he : e ∣ n) (hn : large n) (h7 : e%8=7) : small (n/e) := by
  have eq : ((n/e)%8*(e%8))%8 = n%8 := (Nat.mul_mod _ _ _).symm.trans (congrArg (·%8) (Nat.div_mul_cancel he))
  have b := Nat.mod_lt (n/e) (by decide : 0 < 8)
  rw [h7] at eq
  rcases hn with h|h <;> rw [h] at eq <;> unfold small <;> omega

/-- Multiplication by the coefficient kernel encodes the entire recursion, including the unit divisor. -/
private theorem kernel_row (L : ℕ → ℤ) (h1 : L 1 = 1) : kernel L * row L = seven := by
  ext n
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun t e => kernel L t * row L e)]
  by_cases hr : large n
  · have hn0 : n ≠ 0 := by rcases hr with h|h <;> omega
    have hm : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd _,hn0⟩
    rw [← n.divisors.add_sum_erase (fun t => kernel L t * row L (n/t)) hm]
    have hsf : ∑ t ∈ n.divisors.erase 1, kernel L t * row L (n/t) =
        ∑ t ∈ recursionFactors n, (L t : ZMod 2) * (traceCoefficient L (n/t) : ZMod 2) := by
      rw [←factors_filter hr, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases h : small t <;> by_cases k : large (n/t) <;> simp [kernel,row,h,k]
    rw [hsf]
    simp only [kernel, row,seven,ArithmeticFunction.coe_mk, Nat.div_one, ite_eq_left hr,
      show small 1 by decide,ite_true,h1,Int.cast_one,one_mul]
    rw [traceCoefficient_eq L n,Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_mul,sub_add_cancel]
    unfold baseCoefficient
    split <;> simp
  · have h7 : n%8 ≠ 7 := fun h => hr (Or.inr h)
    simp only [seven,ArithmeticFunction.coe_mk,ite_eq_right h7]
    apply Finset.sum_eq_zero
    intro t ht
    by_cases h : small t
    · have k : ¬ large (n/t) := fun hn => hr (large_of_factors (Nat.mem_divisors.mp ht).1 h hn)
      simp [row,k]
    · simp [kernel,h]

private theorem conv_congr {f g h : AF} {n : ℕ} (H : ∀ t, t ∣ n → f t = g t) : (f*h) n = (g*h) n := by
  rw [ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  have e := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [H p.1 ⟨p.2,e.symm⟩]

/-- The coefficient of (0,0), modulo 2, is one explicit sum over the class-seven divisors. -/
theorem coefficient_mod_two (L : ℕ → ℤ) (h1 : L 1 = 1) {n : ℕ} (hs : Squarefree n)
    (hr : n%8=5 ∨ n%8=7) : (traceCoefficient L n : ZMod 2) =
    ∑ e ∈ n.divisors.filter (fun e => e%8=7), (L (n/e) : ZMod 2) * (genusNumber e : ZMod 2) := by
  have h1' : kernel L 1 = 1 := by simp [kernel,show small 1 by decide,h1]
  calc (traceCoefficient L n : ZMod 2) = (1 * row L) n := by rw [one_mul]; exact (ite_eq_left hr).symm
       _ = ((kernel L * kernel L) * row L) n :=
         conv_congr fun t ht => (square_on_squarefree _ h1' (hs.squarefree_of_dvd ht)).symm
       _ = (kernel L * seven) n := by rw [mul_assoc, kernel_row L h1]
       _ = _ := by
         rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal' (fun t e => kernel L t * seven e), Finset.sum_filter]
         apply Finset.sum_congr rfl
         intro e he
         by_cases h : e%8=7
         · simp [kernel, seven,h,small_of_complement (Nat.mem_divisors.mp he).1 hr h]
         · simp [seven,h]

#print axioms square_on_squarefree
#print axioms coefficient_mod_two
end
end ZInQBlueprint.TYZ.Specialization.TraceAction
