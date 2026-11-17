import ActualOrders
import GlobalOrders
import SelectedTraceCRT

namespace Sun28.QualitativeRows
open ZInQ Sun28.ContactFactors Sun28.ContactSieve Sun28.ScalarPlaces Sun28.FixedPreparation
open Sun28.RealPoleBounds Sun28.GaussianSelection Sun28.SelectedTrace Sun28.Exceptional Sun28.FiniteWitness
open ManuscriptV15.Arithmetic
noncomputable section

open private mod_pos fixed_compatible from ActualOrders
set_option maxHeartbeats 400000

/-- Sun's canonical choice and stronger coprimality conditions pass the exact
graph criterion. This uses the actual scalar and early kernel constraints. -/
theorem balanced_of_orders {ι : Type*} [Fintype ι] (π : ι→Gaussian) (r : ℤ)
    (ray : ∀ i, gaussianCongruent 16 (π i) (9,0)) (o : Orders)
    (lp : o.plusOrder=orderLcm π true) (lm : o.minusOrder=orderLcm π false)
    (ko : o.kernelModulus=kernelMod r) (ts : o.T=supportPlaces r) (ao : o.a=comparisonDepth r) :
    BalancedOrders π r := by
  have nz (i : ι) (s : Bool) : 0<adjacentNorm (π i) s := by
    apply Nat.pos_of_ne_zero
    intro zero
    cases s with
    | false => have hz := (ray_dyadic (ray i)).2; rw [zero,padicValNat_zero_right] at hz; contradiction
    | true => have hz := (ray_dyadic (ray i)).1; rw [zero,padicValNat_zero_right] at hz; contradiction
  obtain ⟨h,L,pos,progress⟩:=o.progression
  have v : o.accepts h := by simpa using progress 0
  have fixed (j : Option ↥(supportPlaces r)) :
      h ≡ (fixedRes r j : ℤ) [ZMOD (fixedMod r j : ℤ)] := by
    cases j with
    | none => simpa only [fixedMod,fixedRes,Nat.cast_zero,ko] using v.preparation
    | some p =>
      have eq := v.localResidue p.val (ts.symm ▸ p.property)
      simpa only [fixedMod,fixedRes,Nat.cast_pow,ao] using eq
  have div := gaussian_crt_divides π o lp lm v
  have left (i : ι) : h ≡ 0 [ZMOD (adjacentNorm (π i) true:ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (div i).1
  have right (i : ι) : h ≡ anchor [ZMOD (adjacentNorm (π i) false:ℤ)] :=
    (Int.modEq_iff_dvd.mpr (div i).2).symm
  exact balanced_of_global (fun i s=>adjacentNorm (π i) s) (fixedMod r) (fixedRes r) (Nat.factorial 576)
    nz (mod_pos r) (fixed_compatible r) (fun _=>true) h fixed left right
end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.balanced_of_orders
