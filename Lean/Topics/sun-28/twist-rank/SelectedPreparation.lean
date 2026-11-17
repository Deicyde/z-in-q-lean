import OrdinaryPrimes

namespace Sun28.TwistRank
open ZInQ Ordinary Forward FixedPreparation PreparedPoles RealPoleBounds
open ScalarHeight Scalar WitnessIndices RealRatio ContactFactors PairedClasses
noncomputable section

def ClassAt (B : ℚ) : Prop := ∀ (m : ℤ) (β θ : ℕ),
    (m:ℚ)∈smallMultipliers → PreparedClasses B m β θ → InputClass β

structure ClassPrepared (B : ℚ) : Prop where
  prepare : Prepared B
  class_at : ClassAt B

structure SelectedAt (w : NinePoints) (x η : ℚ) : Prop where
  guards : Guards w anchor
  scales : ∀ j, (pointScale w fixedMultiplier j)^2*η∉marks ∧
    (pointScale w fixedMultiplier j)^2*η≠3 ∧ pointScale w fixedMultiplier j≠0
  ordinary : ∀ j : Fin 3,
    let A := (pointScale w fixedMultiplier j)^2
    let t := A*η
    let T := ordinaryTraceAt w fixedMultiplier anchor (beta x) A t
    T≠0 ∧ ClassPrepared (detector A t/T^2)
  scalar : let r:=scalarRadicand (beta x)
    let W:=scalarTree r (scalarEntries w fixedMultiplier)
    ∃ δ : ℚ, (δ=1 ∨ δ= -1) ∧ W≠0 ∧ ClassPrepared (signedValue r δ gamma denominator W)

private theorem scalar_ready' (X : ℤ) {w : NinePoints}
    (coeff : ∀ i,|scalarEntries w fixedMultiplier i|≤1)
    (units : ∀ p : ℕ,p.Prime → p∈primes ∨ p∣(integerRadicand X).natAbs →
      let W:=scalarTree (scalarRadicand (beta X)) (scalarEntries w fixedMultiplier)
      W≠0 ∧ padicValRat p W=0) :
    let r:=scalarRadicand (beta X)
    let W:=scalarTree r (scalarEntries w fixedMultiplier)
    ∃ δ : ℚ, (δ=1 ∨ δ= -1) ∧ W≠0 ∧ ClassPrepared (signedValue r δ gamma denominator W) := by
  obtain ⟨δ,sgn,nz,h⟩ := scalar_ready X coeff units
  refine ⟨δ,sgn,nz,h,?_⟩
  intro m β θ member c
  apply Or.inr
  suffices z : δ*scalarRadicand (beta X)=((integerRadicand X).natAbs:ℚ) by
    obtain ⟨pos,kernel⟩:=scalar_class c h.2.1 z
    exact ⟨X,m,pos,member,kernel⟩
  have pos := h.2.1
  change 0 < _^2 * (δ*scalarRadicand (beta X)) at pos
  have z:=pos_of_mul_pos_right pos (sq_nonneg _)
  rw [←cast_radicand] at z ⊢
  change δ*(integerRadicand X:ℤ)=((integerRadicand X).natAbs:ℚ)
  have e : |(integerRadicand X:ℚ)|=((integerRadicand X).natAbs:ℚ) := by
    rw [←Int.cast_abs,←Int.natCast_natAbs,Int.cast_natCast]
  rcases sgn with rfl|rfl
  · simpa only [one_mul] using (abs_of_pos (by simpa using z)).symm.trans e
  · have neg : (integerRadicand X:ℚ)<0 := by linarith
    simpa only [neg_one_mul] using (abs_of_neg neg).symm.trans e

/-- This refinement retains the prime factors and the exact scalar radicand
of the very same four inputs at the very same comparison point. -/
theorem selected_preparation {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit) (select : RaySelection)
    (X : ℤ) : ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, SelectedAt (nineAffine a).doubles (X:ℚ) η := by
  obtain ⟨D,cmin,dp,div,choose⟩:=select X
  obtain ⟨c,q,n,C,dc,cl,cq,betaEq,shift,odds,luc,one,windows⟩:=
    integer_three_pole_windows orbit model X anchor fixedMultiplier D
      (by have := fixed_multiplier_spec.2.1; omega) fixed_multiplier_spec.1 dp div cmin (1/2) (by norm_num)
  obtain ⟨u,v,values,o,rays,vp,large,exclusions,bad,hmin,finite,estimates⟩:=
    choose c q n C dc cl cq betaEq shift odds luc one
  let A:=fixedScale n
  let η:=slope A u v
  obtain ⟨b,L,lp,congr⟩:=o.progression
  obtain ⟨h,k,B,hk,late,out,rep,product,entries,_,_,real⟩:=windows η large b L lp bad finite hmin
  have available:=estimates h B (hk ▸ congr (k:ℤ)) out late rep
  let w:=(nineAffine B).doubles
  have actual (j : Fin 3) : A j=(pointScale w fixedMultiplier j)^2 := by
    unfold A fixedScale pointScale
    rw [product]
  have a0 : A 0=1 := by norm_num [A,fixedScale,scaleRoot]
  have positive := actual_scales_positive n (fun i => (odds i).1.ne')
  refine ⟨B,η,point_guards rep,?_,?_,scalar_ready' X entries available.scalar_units⟩
  · intro j
    exact ⟨(real j).1,(real j).2.1,fun z => (positive j).ne' (by change A j=0; rw [actual j,z];norm_num)⟩
  · intro j
    rw [←actual j]
    have rt:=real j
    rw [←actual j] at rt
    obtain ⟨_,_,_,_,tracepos,Bpos,Bsmall⟩:=rt
    have ea : argument A u v j=A j*η := argument_eq ..
    have tu:=available.trace_orders j
    have de:=available.trace_depths j
    dsimp only at tu de
    rw [ea] at tu de
    refine ⟨tracepos.ne',?_⟩
    rw [←ea] at tu de Bpos Bsmall tracepos ⊢
    have prep := prepared_detector values a0 vp j (positive j).ne' tracepos.ne' (exclusions j) tu
      ⟨Bpos,(Rat.cast_lt (K:=ℝ)).1 (by simpa only [A,beta,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using Bsmall)⟩ de
    exact ⟨prep,fun _ _ _ member classes=>Or.inl (ordinary_prime_shape values rays vp j (positive j).ne' member classes prep.2.1)⟩

end
end Sun28.TwistRank
#print axioms Sun28.TwistRank.selected_preparation
