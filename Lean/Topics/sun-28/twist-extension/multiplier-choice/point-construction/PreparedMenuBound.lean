import PreparedArithmeticProgression
import PolynomialBranchTests

namespace Sun28.PointConstruction
open Filter RatFunc Sun28.Ordinary Sun28.ScalarHeight Sun28.TwistRank Sun28.FixedPreparation
noncomputable section

def fractional (a b c d : ℚ) (n:ℕ) : ℚ := (a*(n:ℚ)+b)/(c*(n:ℚ)+d)

/-- The finite exceptional set includes poles and points deleted from the defining open set. -/
noncomputable def squareHits (f : Finset Functions) (extra : Finset ℚ) (a b c d:ℚ)
    (N:ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun n =>
    fractional a b c d n ∈ extra ∨ ∃g∈f, IsSquare (value g (fractional a b c d n))

/-- The one-dimensional integral thin-set estimate in Serre, Topics in Galois Theory,
Theorem 3.4.4 (Cohen), applied to finitely many quadratic covers and a change of parameter. -/
def PublishedCohen : Prop := ∀ (f : Finset Functions), (∀g∈f, ¬IsSquare g) →
  ∀ (extra : Finset ℚ) (a b c d:ℚ), a*d-b*c≠0 →
    ∃ M:ℝ, 0 ≤ M ∧ ∀ N:ℕ, 2 ≤ N →
      ((squareHits f extra a b c d N).card:ℝ) ≤ M*Real.sqrt N*Real.log N

theorem fractional_progression (n : ℕ) :
    fractional 0 gamma (7895415*gamma) (1+2*(7895415*gamma)) n=progression (n:ℤ) := by
  unfold fractional progression progressionDen
  push_cast;ring

def accepted (r : WitnessRow) (x:ℚ) : Prop :=
  poleBranch r.multiplier (inputB x) (value r.first x) (value r.ratio x)

noncomputable def menuHits {ι:Type*} [Fintype ι] (rows : ι→WitnessRow) (N:ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun n => ∃i, accepted (rows i) (progression n)

/-- Outside a finite exceptional set, any accepted abscissa lies under one of a fixed
finite set of genuinely quadratic covers; both square roots may be chosen afresh. -/
theorem menu_thin {ι:Type*} [Fintype ι] (rows : ι→WitnessRow) :
    ∃ f:Finset Functions, (∀g∈f, ¬IsSquare g) ∧ ∃ extra:Finset ℚ, ∀x:ℚ,
    (∃ i, accepted (rows i) x) → x∈extra ∨ ∃g∈f, IsSquare (value g x) := by
  classical
  let pool : Finset Functions :=
    (Finset.univ.image fun i=>(rows i).leftRad) ∪ (Finset.univ.image fun i=>(rows i).rightRad)
  let f := pool.filter fun g=> ¬ IsSquare g
  let P (x:ℚ) := ∀i, accepted (rows i) x → value (rows i).guard x≠0 ∧
    IsSquare (value (rows i).leftRad x) ∧ IsSquare (value (rows i).rightRad x)
  have ev : ∀ᶠ x:ℚ in cofinite, P x :=
    Filter.eventually_all.mpr fun i=>(rows i).specialization
  have finite := Filter.eventually_cofinite.mp ev
  refine ⟨f,fun _ hg=>(Finset.mem_filter.mp hg).2,finite.toFinset,?_⟩
  intro x witness
  by_cases good : P x
  · right
    obtain ⟨i,ok⟩:=witness
    obtain ⟨gn,la,rb⟩:=good i ok
    have active : (rows i).guard≠0 := by
      intro z
      rw [z] at gn
      exact gn (RatFunc.eval_zero _ _)
    rcases (rows i).nonsquare_choice active with left | right
    · exact ⟨(rows i).leftRad,Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)),left⟩,la⟩
    · exact ⟨(rows i).rightRad,Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)),right⟩,rb⟩
  · exact Or.inl (finite.mem_toFinset.mpr good)

/-- The number of class-prepared scalar values furnished by a fixed finite menu up to N. -/
theorem prepared_menu_bound (published:PublishedCohen) {ι:Type*} [Fintype ι]
    (rows : ι→WitnessRow) : (∀ n:ℕ,ClassPrepared (inputB (progression n))) ∧
    ∃ M:ℝ, 0≤M ∧ ∀ N:ℕ, 2≤N → ((menuHits rows N).card:ℝ) ≤ M*Real.sqrt N*Real.log N := by
  classical
  refine ⟨progression_prepared,?_⟩
  obtain ⟨f,hf,extra,cover⟩:=menu_thin rows
  let c:ℚ := 7895415*gamma
  let d:ℚ := 1+2*c
  have nondeg : (0:ℚ)*d-(gamma:ℚ)*c≠0 := by
    have pos : 0<(gamma:ℚ) := by exact_mod_cast gamma_positive
    dsimp [c];simp only [zero_mul,zero_sub,neg_ne_zero];positivity
  obtain ⟨M,mp,bnd⟩:=published f hf extra 0 gamma c d nondeg
  refine ⟨M,mp,fun N nbig=>le_trans ?_ (bnd N nbig)⟩
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨less,yes⟩:=Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨less,?_⟩
  rw [show fractional 0 gamma c d n=progression n from fractional_progression n]
  exact cover _ yes

end
end Sun28.PointConstruction
#print axioms Sun28.PointConstruction.fractional_progression
#print axioms Sun28.PointConstruction.menu_thin
#print axioms Sun28.PointConstruction.prepared_menu_bound
