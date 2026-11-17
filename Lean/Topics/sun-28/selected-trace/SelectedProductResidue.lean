import OrdinaryTrace
import OrdinaryAnchors

/-! The residue of an inverse ordinary weight at a detector of order one. -/
namespace Sun28.SelectedTrace
open Sun28.ScalarTrace Sun28.Ordinary
open scoped Classical
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))

/-- At a detector of order one the inverse leaf is congruent to the indicator
of success. A zero test succeeds. -/
theorem inverse_factor_residue {r D : K} (hr : v r=1) (k : ℕ) :
    Near v 1 (factor r D k)⁻¹ (if (k:WithTop ℤ)≤v D then 1 else 0) := by
  classical
  by_cases zero : D=0
  · simp [zero,factor,Near]
  obtain ⟨d,hd⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr zero)
  have vd := hd.symm
  have valuation {α : ℤ} (h : v r=(α:WithTop ℤ)) :
      v (r*(D/r^k)^2)=((α+2*(d-(k:ℤ)*α):ℤ):WithTop ℤ) := by
    simp only [v.map_mul,v.map_div,v.map_pow,h,vd,←WithTop.coe_nsmul]
    congr 1
  have term : v (r*(D/r^k)^2)=((1+2*(d-(k:ℤ)):ℤ):WithTop ℤ) := by
    simpa using (valuation (α:=1) hr)
  by_cases good : (k:WithTop ℤ)≤v D
  · rw [ite_eq_left good]
    have dg : (k:ℤ)≤d := WithTop.coe_le_coe.mp (vd ▸ good)
    have depth : (1:WithTop ℤ)≤v (r*(D/r^k)^2) := by
      rw [term]; exact WithTop.coe_le_coe.mpr (show (1:ℤ)≤1+2*(d-(k:ℤ)) by omega)
    have lower : v (1:K)<v (r*(D/r^k)^2) := by rw [v.map_one]; exact (by decide : (0:WithTop ℤ)<1).trans_le depth
    have unit : v (factor r D k)=0 := (v.map_add_eq_of_lt_left lower).trans v.map_one
    have nz : factor r D k≠0 := (AddValuation.ne_top_iff v).mp (by rw [unit]; decide)
    have inv_eq : (factor r D k)⁻¹-1 = -(r*(D/r^k)^2)/(factor r D k) := by
      field_simp [nz]
      unfold factor
      ring
    simpa only [Near,Int.cast_one,Nat.cast_one,inv_eq,v.map_div,v.map_neg,unit,sub_zero] using depth
  · rw [ite_eq_right good]
    have dg : d<(k:ℤ) := lt_of_not_ge (fun ge => good (vd ▸ WithTop.coe_le_coe.mpr ge))
    have lower : v (r*(D/r^k)^2)<v (1:K) := by
      rw [v.map_one,term]; exact WithTop.coe_lt_coe.mpr (show 1+2*(d-(k:ℤ))<0 by omega)
    have vf : v (factor r D k)=((1+2*(d-(k:ℤ)):ℤ):WithTop ℤ) :=
      (v.map_add_eq_of_lt_right lower).trans term
    simp only [Near,Int.cast_zero,sub_zero,Nat.cast_one,v.map_inv,vf,←WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact WithTop.coe_le_coe.mpr (show (1:ℤ)≤ -(1+2*(d-(k:ℤ))) by omega)

variable {I : Type*}

/-- The inverse of a finite weight has residue one precisely when every test
succeeds, and residue zero if any one fails. -/
theorem inverse_partial_residue {r : K} (hr : v r=1) (D : I→K) (k : I→ℕ) (s : Finset I) :
    Near v 1 (∏ i ∈ s, factor r (D i) (k i))⁻¹
      (if ∀ i∈s, (k i:WithTop ℤ)≤v (D i) then 1 else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Near]
  | @insert a s ha ih =>
    have one := inverse_factor_residue v (D:=D a) hr (k a)
    have both := one.mul v ih
    by_cases h : (k a:WithTop ℤ)≤v (D a) <;>
      by_cases j : ∀ i∈s, (k i:WithTop ℤ)≤v (D i) <;>
        simpa only [Finset.prod_insert ha,mul_inv,Finset.forall_mem_insert,h,j,
          true_and,and_true,false_and,and_false,ite_true,ite_false,one_mul,zero_mul,mul_zero] using both

variable [Fintype I] [CharZero K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K]

/-- The actual rational field trace reduces to the sum of the two success
indicators. Both products use the same rational detector. -/
theorem ordinary_trace_residue (σ : K ≃ₐ[ℚ] K) (hs : σ≠1) (r : ℚ)
    (hr : v (algebraMap ℚ K r)=1) (D : I→K) (k : I→ℕ) :
    Near v 1 (algebraMap ℚ K (ordinaryTrace r D k))
      ((if ∀ i, (k i:WithTop ℤ)≤v (D i) then 1 else 0) +
       (if ∀ i, (k i:WithTop ℤ)≤v (σ (D i)) then 1 else 0)) := by
  classical
  rw [ordinaryTrace_eq σ hs]
  have first := inverse_partial_residue v hr D k Finset.univ
  have second := inverse_partial_residue v hr (fun i => σ (D i)) k Finset.univ
  simpa only [Finset.mem_univ,true_implies,weightProduct] using first.add v second

/-- At an odd place one successful branch prevents cancellation in the
rational trace, even if the other branch has deficient tests. -/
theorem ordinary_trace_unit (σ : K ≃ₐ[ℚ] K) (hs : σ≠1) (r : ℚ)
    (hr : v (algebraMap ℚ K r)=1) (two : v (2:K)=0) (D : I→K) (k : I→ℕ)
    (success : (∀ i, (k i:WithTop ℤ)≤v (D i)) ∨ (∀ i, (k i:WithTop ℤ)≤v (σ (D i)))) :
    v (algebraMap ℚ K (ordinaryTrace r D k))=0 := by
  classical
  let T:=algebraMap ℚ K (ordinaryTrace r D k)
  have conclude (z : ℤ) (near : Near v 1 T z) (unit : v (z:K)=0) : v T=0 := by
    have strict : v (z:K)<v (T-(z:K)) := by
      rw [unit]; exact (by decide : (0:WithTop ℤ)<1).trans_le near
    exact (v.map_eq_of_lt_sub strict).trans unit
  have residue := ordinary_trace_residue v σ hs r hr D k
  by_cases h : ∀ i, (k i:WithTop ℤ)≤v (D i) <;>
    by_cases j : ∀ i, (k i:WithTop ℤ)≤v (σ (D i))
  · apply conclude 2
    · simpa [h,j,T] using residue
    · simpa using two
  · apply conclude 1
    · simpa [h,j,T] using residue
    · simp
  · apply conclude 1
    · simpa [h,j,T] using residue
    · simp
  · exact False.elim (success.elim h j)

end Sun28.SelectedTrace
#print axioms Sun28.SelectedTrace.inverse_factor_residue
#print axioms Sun28.SelectedTrace.inverse_partial_residue
#print axioms Sun28.SelectedTrace.ordinary_trace_residue
#print axioms Sun28.SelectedTrace.ordinary_trace_unit
