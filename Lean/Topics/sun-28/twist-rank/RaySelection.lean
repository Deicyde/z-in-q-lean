import FiniteWitness

namespace Sun28.TwistRank
open IsDedekindDomain NumberField
open scoped NumberField
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.PreparedPoles Sun28.RealPoleBounds
open Sun28.ScalarHeight Sun28.WitnessIndices Sun28.ContactFactors Sun28.ScalarPlaces
open Sun28.GaussianSelection Sun28.Exceptional Sun28.SelectedTrace Sun28.RealRatio
open ManuscriptV15.Arithmetic
noncomputable section

open Sun28.FiniteWitness

/-- The uniform size and two rational norm rays retained at every marked shift. -/
def RayValues {A : Fin 3→ℚ} {u v : ℕ} (h : PrimeValues A u v) : Prop :=
  ∀ d∈shifts A,65<h.value d ∧ h.value d%16=1 ∧ h.value d%7=3

private theorem note_ray_norm {z : Gaussian} (r16 : gaussianCongruent 16 z (9,0))
    (r7 : gaussianCongruent 7 z (1,3)) :
    gaussianNorm z%16=1 ∧ gaussianNorm z%7=3 := by
  have nz : (gaussianNorm z:ℤ)=z.1^2+z.2^2 := by
    unfold gaussianNorm; rw [Int.natCast_natAbs,abs_of_nonneg (by positivity)]
  obtain ⟨a,b⟩:=r16
  obtain ⟨c,d⟩:=r7
  change z.1 ≡ 9 [ZMOD 16] at a
  change z.2 ≡ 0 [ZMOD 16] at b
  change z.1 ≡ 1 [ZMOD 7] at c
  change z.2 ≡ 3 [ZMOD 7] at d
  have e : (gaussianNorm z:ℤ) ≡ 1 [ZMOD 16] := by
    rw [nz]; exact ((a.pow 2).add (b.pow 2)).trans (by decide)
  have f : (gaussianNorm z:ℤ) ≡ 3 [ZMOD 7] := by
    rw [nz]; exact ((c.pow 2).add (d.pow 2)).trans (by decide)
  exact ⟨Int.natCast_modEq_iff.mp e,Int.natCast_modEq_iff.mp f⟩

/-- The same selection in the same quantifier order, retaining the ray records. -/
def RaySelection : Prop :=
  ∀ X : ℤ, ∃ (D : ℕ) (cmin : ℤ), 0<D ∧ fixedMultiplier∣D ∧
    ∀ (c q : ℤ) (n : Fin 4→ℤ) (C : ℝ), (D:ℤ)∣c → max cmin 0<c → c=(fixedMultiplier:ℤ)*q →
      n 0=2*X^2+3 → n 1=c+1 → (∀ i,0<n i ∧ Odd (n i)) → lucas (n 1) (n 2) (n 3)=0 → 1≤C →
      let A:=fixedScale n
      ∃ (u v : ℕ) (values : PrimeValues A u v) (o : Orders), RayValues values ∧ 0<v ∧
        slopeThreshold A C (1/2)<(slope A u v:ℝ) ∧
        (∀ j,∀ p∈selected values j, ¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0) ∧
        ∃ (bad : Set ℤ) (hmin : ℤ), bad.Finite ∧ ∀ (h : ℤ) (B : Fin 9→AffineInput),
          o.accepts h → h∉bad → max (max anchor hmin) 0<h →
          Consequences (nineAffine B).doubles fixedMultiplier anchor ⟨q,h,n,fun i=>h*n i⟩ →
          LocalEstimates X A u v values (nineAffine B).doubles

private theorem rays_of_tests (sieve : ContactSieve.PrimePatterns) (integral : FiniteWitness.IntegralTests) : RaySelection := by
  classical
  intro X
  let r:=integerRadicand X
  let T:=supportPlaces r
  let κ:=kernelMod r
  let a:=comparisonDepth r
  let M:=fixedMultiplier
  have mp : 0<M := by have := fixed_multiplier_spec.2.1; change 0<fixedMultiplier; omega
  obtain ⟨dp,mdiv,_⟩ := step_spec r mp
  refine ⟨stepMod r M,0,dp,mdiv,?_⟩
  intro c q n C dc cl cq first shift odds luc _one
  let A:=fixedScale n
  have unitScale : A 0=1 := by norm_num [A,fixedScale,scaleRoot]
  have alive : ∀ j,A j≠0 := fun j => (actual_scales_positive n (fun i=>(odds i).1.ne') j).ne'
  have two : 2∈T := Finset.mem_union_left _ (by decide : 2∈primes)
  obtain ⟨u,v,values,π,o,_,vp,dv,large,ahead,exclude,oriented,lp,lm,ko,ts,ao⟩ :=
    ContactSieve.select_with_orders sieve (X:=X) (c:=c) (q:=q) (n:=n)
      ⟨by omega,cq,first,shift,odds,luc⟩ (requiredDivisor A) κ T a (divisor_positive A)
      (kernel_positive r) (fun _ => support_prime) two (fun _ _ => by dsimp [κ,a,comparisonDepth]; omega)
      (by dsimp [a,comparisonDepth]; omega) (slopeThreshold A C (1/2)) (selectionBound T)
  have rays : RayValues values := by
    intro d hd
    have h:=note_ray_norm (oriented.ray16 ⟨d,hd⟩) (oriented.ray7 ⟨d,hd⟩)
    rw [oriented.norm] at h
    exact ⟨(separated_values values T ahead).1 d hd,h⟩
  refine ⟨u,v,values,o,rays,vp,large,exclude,∅,0,Set.finite_empty,?_⟩
  intro h B crt _out _late rep
  have big := (separated_values values T ahead).1
  have betaEq : beta X=(n 0:ℚ) := by rw [first]; simp [beta]
  have divide : (κ:ℤ)∣h := by
    have d:=Int.modEq_zero_iff_dvd.mp crt.preparation
    simpa only [ko] using d
  have ah : anchor∣h := (Int.natCast_dvd_natCast.mpr (dvd_mul_right _ _ :
    Nat.factorial 576∣kernelMod r)).trans divide
  constructor
  · intro j t trace p hp
    have all:=selected_trace_orders values unitScale alive vp π o lp lm big exclude (fun d => by
      have := Fact.mk (values.prime _ d.property)
      obtain ⟨z,z2,plus,minus⟩:=CMReduction.exists_oriented_root (oriented.norm d) (oriented.ray16 d) (oriented.ray7 d)
      exact ⟨z,z2,Or.inl ⟨plus,minus⟩⟩) crt rep luc betaEq
    exact (all j p hp).2.1.le
  · apply fixed_depths values alive vp big dv
    intro p fix prime place lie
    rw [betaEq]
    exact integral p prime fix place lie _ _ q h (n 0) n rep ah
  · intro p prime inSet
    have pp : p∈T := by
      rcases inSet with a|b
      · exact Finset.mem_union_left _ a
      · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨prime,b,Int.natAbs_ne_zero.mpr (radicand_nonzero X)⟩)
    have ep := (crt.exact_depth prime (ts.symm ▸ pp)).2
    rw [ao] at ep
    rw [←cast_radicand]
    exact scalar_unit_of_indices (radicand_nonzero X) pp mp rep (by change n 1-1=c; omega) divide dc ep

theorem ray_selection (sieve : ContactSieve.PrimePatterns) : RaySelection := by
  apply rays_of_tests sieve
  intro p prime fixed place lie w M q h β n rep hh
  let _ : Fact p.Prime := ⟨prime⟩
  let _ : place.asIdeal.LiesOver (basePrime p prime).asIdeal := lie
  exact OrdinaryIntegrality.ordinaryAt_integral fixed place rep β (dvd_refl _) hh (fun _ => rfl)

end
end Sun28.TwistRank
#print axioms Sun28.TwistRank.ray_selection
