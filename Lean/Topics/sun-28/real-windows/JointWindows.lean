import FiniteWindows
import OrdinaryReadouts

/-! Real part of Sun's simultaneous completeness construction. The scalar
index is selected before the four roots. The ordinary bound is selected before
the prime parameters and every possible signed congruence progression. -/
namespace Sun28.RealWindows
open Filter Set NumberField ZInQ ZInQ.Mult Sun28.RealRatio Sun28.Scalar Sun28.Ordinary Sun28.Forward
open Sun28.FixedPreparation Sun28.WitnessIndices
open scoped Topology
noncomputable section

private theorem bound_at_places {x : K0} {B : ℝ}
    (all : ∀ σ : K0 →+* ℝ,|σ x| ≤ B) : ∀ ν : InfinitePlace K0, ν x≤B := by
  classical
  intro ν
  have m : ν∈(Finset.univ : Finset (InfinitePlace K0)):=Finset.mem_univ _
  rw [infinitePlace_K0.1] at m
  obtain rfl|p:=Finset.mem_insert.mp m
  · simpa only [wPlus_apply] using all K0.embPlus
  · obtain rfl:=Finset.mem_singleton.mp p
    simpa only [wMinus_apply] using all K0.embMinus

/-- The two denominator guards of equation (4.4) hold for every sufficiently large h. -/
theorem denominator_guards (anchor h : ℤ) (late : max anchor 0 < h) :
    truncAt (h • P)≠0 ∧ conjugation (truncAt ((h-anchor) • P))≠0 := by
  exact ⟨truncAt_multiple_nonzero _ (by omega), (map_ne_zero conjugation).2
    (truncAt_multiple_nonzero _ (by omega))⟩

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalAddGroup G]

/-- For every integer input and its four later fixed roots, C is independent of
slope, prime sizes and the resulting CRT progression. The same h gives the
ratio in both real embeddings and all sixteen field-valued ordinary bounds. -/
theorem choose_shared_readouts (a : Orbit G) (model : ParameterModel a) (anchor : ℤ) :
    ∃ d : ℝ,0<d ∧
    ∀ (D : ℕ),0<D → ∀ cmin : ℤ,∃ (c : ℤ) (u : ℕ),
      c=(D:ℤ)*u ∧ max cmin 0<c ∧
      (∀ σ : K0 →+* ℝ, |σ (zAt c)| < d) ∧
      ∀ (n : Fin 4→ℤ) (β : ℚ),∃ C : ℝ,1≤C ∧
      ∀ (h₀ : ℤ) (L : ℕ),0<L → ∀ (bad : Set ℤ),bad.Finite → ∀ hmin : ℤ,
      ∃ (h : ℤ) (k : ℕ),h=h₀+(L:ℤ)*k ∧ max (max anchor hmin) 0<h ∧ h∉bad ∧
        (∀ σ : K0 →+* ℝ, |σ (zAt c)| < |σ (zAt h)|) ∧
        (truncAt (h • P)≠0 ∧ conjugation (truncAt ((h-anchor) • P))≠0) ∧
        ∀ i, (∀ σ : K0 →+* ℝ, |σ (ordinaryTests sqrt2_sq conjugation anchor h n (fun j=>h*n j) β i)| ≤ C) ∧
          ∀ ν : InfinitePlace K0, ν (ordinaryTests sqrt2_sq conjugation anchor h n (fun j=>h*n j) β i)≤C := by
  classical
  obtain ⟨d,dp,ch⟩:=finite_windows a model anchor
  refine ⟨d,dp,?_⟩
  intro D dpos cm
  obtain ⟨c,u,eq,high,small,rest⟩:=ch D dpos cm
  refine ⟨c,u,eq,high,small,?_⟩
  intro n β
  let F (t : Bool × OrdinaryTest) := varyingReadout model (place t.1) anchor n β t.2
  let : Nonempty (Bool × OrdinaryTest) := ⟨(false,.h)⟩
  obtain ⟨C,one,choose⟩:=rest F (fun i m hi=>varyingReadout_continuousAt model _ _ _ _ _ m hi)
  refine ⟨C,one,?_⟩
  intro h₀ L lpos bad fb hm
  obtain ⟨h,k,e,hl,out,hr,bound⟩:=choose h₀ L lpos bad fb hm
  have all (σ : K0 →+* ℝ) : ∀ i,|σ (ordinaryTests sqrt2_sq conjugation anchor h n (fun j=>h*n j) β i)| ≤ C := by
    apply ordinary_from_readouts model _ _ _ _ _ one
    intro i
    obtain rfl|rfl:=embedding_cases σ
    · exact bound (false,i)
    · exact bound (true,i)
  exact ⟨h,k,e,hl,out,hr,denominator_guards _ _ (by omega),fun i => ⟨fun σ=>all σ i,
    bound_at_places (fun σ=>all σ i)⟩⟩

omit [CompactSpace G] [IsTopologicalAddGroup G] in
/-- At represented nine-point data with the chosen indices, the same H serves
the scalar six and the ordinary sixteen. This is the literal ordinaryAt. -/
theorem shared_point_bounds {w : NinePoints} {M : ℕ} {anchor : ℤ} {l : Labels}
    (rep : Consequences w M anchor l) {c h : ℤ} (cvalue : l.n 1-1=c) (hvalue : l.h=h)
    (mult : ∀ i,l.m i=h*l.n i) (β : ℚ) (C : ℝ)
    (ratio : ∀ σ : K0 →+* ℝ, |σ (zAt c)| < |σ (zAt h)|)
    (ordinary : ∀ i,∀ σ : K0 →+* ℝ, |σ (ordinaryTests sqrt2_sq conjugation anchor h l.n (fun j=>h*l.n j) β i)| ≤ C) :
    (∀ i, |scalarEntries w M i|≤1) ∧
      (truncAt w.H≠0 ∧ conjugation (truncAt (translatedBase w anchor))≠0) ∧
      (∀ i,∀ σ : K0 →+* ℝ, |σ (ordinaryAt w M anchor β i)|≤C) ∧
      ∀ i,∀ ν : InfinitePlace K0, ν (ordinaryAt w M anchor β i)≤C := by
  have v (i : OrdinaryTest) (σ : K0 →+* ℝ) : |σ (ordinaryAt w M anchor β i)|≤C := by
    rw [←ordinaryAt_eq rep,hvalue,funext mult]
    exact ordinary i σ
  exact ⟨entries_on_shared_indices rep cvalue hvalue ratio,both_denominators rep,
    v,fun i=>bound_at_places (v i)⟩

end
end Sun28.RealWindows
#print axioms Sun28.RealWindows.denominator_guards
#print axioms Sun28.RealWindows.choose_shared_readouts
#print axioms Sun28.RealWindows.shared_point_bounds
