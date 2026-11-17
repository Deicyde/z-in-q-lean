import LocalSelection

namespace Sun28.ContactFactors
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.PreparedPoles Sun28.RealPoleBounds
open Sun28.ScalarHeight Sun28.Scalar Sun28.WitnessIndices Sun28.RealRatio
noncomputable section

theorem point_guards {w : NinePoints} {M : ℕ} {b : ℤ} {l : Labels}
    (h : Consequences w M b l) : Guards w b := by
  have nz {m : ℤ} (e : m≠0) : m • P ≠ 0 := fun z => e (index_injective (z.trans (zero_zsmul P).symm))
  have root (j : Fin 4) : OddChart (rootPoints w M j) :=
    h.represented.root_point j ▸ chart_of_odd (h.odd j)
  exact ⟨h.represented.q_point ▸ nz h.q_nonzero,h.represented.h_point ▸ nz h.h_nonzero,
    h.base_point ▸ nz h.base_nonzero,root 0,root 2,root 3⟩

theorem scalar_ready (X : ℤ) {w : NinePoints}
    (coeff : ∀ i,|scalarEntries w fixedMultiplier i|≤1)
    (units : ∀ p : ℕ, p.Prime → p∈primes ∨ p∣(integerRadicand X).natAbs →
      let W:=scalarTree (scalarRadicand (beta X)) (scalarEntries w fixedMultiplier)
      W≠0 ∧ padicValRat p W=0) :
    let r:=scalarRadicand (beta X)
    let W:=scalarTree r (scalarEntries w fixedMultiplier)
    ∃ δ : ℚ, (δ=1 ∨ δ= -1) ∧ W≠0 ∧ Prepared (signedValue r δ gamma denominator W) := by
  obtain ⟨δ,sign,absolute,eqn,large⟩ := signed_radicand X
  have nonzero := (units 2 Nat.prime_two (Or.inl (by decide))).1
  exact ⟨δ,sign,nonzero,FinitePole.scalar_prepared absolute (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr
    (radicand_nonzero X))) nonzero (fun p pp mem => (units p pp mem).2)
    (scalar_real_preparation _ _ _ large eqn coeff nonzero)⟩

theorem preparation_from_selection {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit) (select : FiniteSelection) :
    IntegerPreparation := by
  intro X
  obtain ⟨D,cmin,dp,div,choose⟩:=select X
  obtain ⟨c,q,n,C,dc,cl,cq,betaEq,shift,odds,luc,one,windows⟩:=
    integer_three_pole_windows orbit model X anchor fixedMultiplier D
      (by have := fixed_multiplier_spec.2.1; omega) fixed_multiplier_spec.1 dp div cmin (1/2) (by norm_num)
  obtain ⟨u,v,values,o,vp,large,exclusions,bad,hmin,finite,estimates⟩:=
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
  refine ⟨B,η,point_guards rep,?_,?_,scalar_ready X entries available.scalar_units⟩
  · intro j
    exact ⟨(real j).1,(real j).2.1,fun z => (positive j).ne' (by change A j=0; rw [actual j,z];norm_num)⟩
  · intro j
    rw [← actual j]
    have rt:=real j
    rw [← actual j] at rt
    obtain ⟨_,_,_,_,tracepos,Bpos,Bsmall⟩:=rt
    have argument_at : argument A u v j=A j*η := argument_eq .. 
    have tu := available.trace_orders j
    have de := available.trace_depths j
    dsimp only at tu de
    rw [argument_at] at tu de
    refine ⟨tracepos.ne',?_⟩
    rw [← argument_at] at tu de Bpos Bsmall tracepos ⊢
    refine prepared_detector values a0 vp j (positive j).ne' tracepos.ne' (exclusions j) tu
      ⟨Bpos,?_⟩ de
    exact (Rat.cast_lt (K:=ℝ)).1 (by simpa only [A,beta,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using Bsmall)

/-- The exact fixed polynomial from standard real geometry and the identified
global arithmetic inputs. All quantifiers share the same slope and comparison point. -/
theorem projection_from_selection {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit)
    (units : FiveMarkUnits.PublishedCorollary72) (height : MinimalConductors.ExactLeastHeight)
    (select : FiniteSelection) (twists : ManuscriptV15.Arithmetic.SimultaneousTwists) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  projection_of_manuscript_twists units height (preparation_from_selection orbit model select) twists x

end
end Sun28.ContactFactors
#print axioms Sun28.ContactFactors.point_guards
#print axioms Sun28.ContactFactors.scalar_ready
#print axioms Sun28.ContactFactors.preparation_from_selection
#print axioms Sun28.ContactFactors.projection_from_selection
