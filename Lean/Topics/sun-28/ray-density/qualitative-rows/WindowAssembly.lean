import SingleWindow

namespace Sun28.QualitativeRows
open IsDedekindDomain NumberField
open scoped NumberField
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.PreparedPoles Sun28.RealPoleBounds
open Sun28.ScalarHeight Sun28.Scalar Sun28.WitnessIndices Sun28.ContactFactors Sun28.ScalarPlaces
open Sun28.GaussianSelection Sun28.Exceptional Sun28.SelectedTrace Sun28.RealRatio
open Sun28.PairedClasses Sun28.TwistRank Sun28.FiniteWitness Sun28.ContactSieve ManuscriptV15.Arithmetic
noncomputable section

open private scalar_ready' from SelectedPreparation
open private note_ray_norm from RaySelection

/-- The common integer preparation needs a residue class for the rational primes
and a progression on which the actual selected trace has order zero. -/
def TraceProgression {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (w : Window X) : Prop :=
  ∃ (b : ℤ) (L : ℕ), 0<L ∧ ∀ k : ℤ, let h:=b+(L:ℤ)*k
    (kernelMod (integerRadicand X):ℤ)∣h ∧
    (∀ p∈supportPlaces (integerRadicand X), h ≡ (p:ℤ)^comparisonDepth (integerRadicand X) p
      [ZMOD (p:ℤ)^(comparisonDepth (integerRadicand X) p+1)]) ∧
    ∀ (B : Fin 9→AffineInput), Consequences (nineAffine B).doubles fixedMultiplier anchor
      ⟨w.q,h,w.n,fun i=>h*w.n i⟩ →
      ∀ j, ∀ p∈selected values j, padicValRat p (ordinaryTraceAt (nineAffine B).doubles fixedMultiplier
        anchor (beta X) (A j) (argument A u v j))=0

theorem selected_of_progression {X : ℤ} (window : Window X) {u v : ℕ}
    (values : PrimeValues (fixedScale window.n) u v) (vp : 0<v) (dv : requiredDivisor (fixedScale window.n)∣v)
    (large : slopeThreshold (fixedScale window.n) window.C (1/2)<(slope (fixedScale window.n) u v:ℝ))
    (rays : RayValues values)
    (exclude : ∀ j,∀ p∈selected values j,¬p∣dilation (fixedScale window.n) ∧ ¬p∣separation ∧
      padicValRat p (fixedScale window.n j)=0)
    (progress : TraceProgression values window) :
    ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, SelectedAt (nineAffine a).doubles (X:ℚ) η := by
  let r:=integerRadicand X
  let A:=fixedScale window.n
  let η:=slope A u v
  have roots:=window.roots
  have odds:=roots.odd
  have positive := actual_scales_positive window.n (fun i => (odds i).1.ne')
  have alive : ∀ j,A j≠0 := fun j => (positive j).ne'
  have a0 : A 0=1 := by norm_num [A,fixedScale,scaleRoot]
  have big d (mem : d∈shifts A) : 65<values.value d := (rays d mem).1
  obtain ⟨b,L,lp,congr⟩:=progress
  obtain ⟨h,k,B,hk,rep,product,entries,real⟩:=window.progression η large b L lp
  obtain ⟨divide,localRes,success⟩ := hk ▸ congr (k:ℤ)
  have mp : 0<fixedMultiplier := by have := fixed_multiplier_spec.2.1; omega
  have ah : anchor∣h := (Int.natCast_dvd_natCast.mpr (dvd_mul_right _ _ :
    Nat.factorial 576∣kernelMod r)).trans divide
  have betaEq : beta X=(window.n 0:ℚ) := by rw [roots.beta]; simp [beta]
  let w:=(nineAffine B).doubles
  have available : LocalEstimates X A u v values w := by
    constructor
    · intro j t trace p hp
      exact (success B rep j p hp).le
    · apply fixed_depths values alive vp big dv
      intro p fixed prime place lie
      rw [betaEq]
      let _ : Fact p.Prime := ⟨prime⟩
      let _ : place.asIdeal.LiesOver (basePrime p prime).asIdeal := lie
      exact OrdinaryIntegrality.ordinaryAt_integral fixed place rep (window.n 0) (dvd_refl _) ah (fun _ => rfl)
    · intro p prime inSet
      have pp : p∈supportPlaces r := by
        rcases inSet with a|b
        · exact Finset.mem_union_left _ a
        · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨prime,b,Int.natAbs_ne_zero.mpr (radicand_nonzero X)⟩)
      have ep := (ComparisonCRT.exact_order prime (localRes p pp)).2
      rw [←cast_radicand]
      exact scalar_unit_of_indices (radicand_nonzero X) pp mp rep
        (by change window.n 1-1=window.c;rw [roots.shift];ring) divide window.early ep
  have actual (j : Fin 3) : A j=(pointScale w fixedMultiplier j)^2 := by
    unfold A fixedScale pointScale
    rw [product]
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
    have prep := prepared_detector values a0 vp j (positive j).ne' tracepos.ne' (exclude j) tu
      ⟨Bpos,(Rat.cast_lt (K:=ℝ)).1 (by simpa only [A,beta,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using Bsmall)⟩ de
    exact ⟨prep,fun _ _ _ member classes=>Or.inl (ordinary_prime_shape values rays vp j (positive j).ne' member classes prep.2.1)⟩


end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.selected_of_progression

