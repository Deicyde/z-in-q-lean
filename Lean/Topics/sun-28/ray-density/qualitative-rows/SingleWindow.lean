import ChosenRoots
import SelectedPreparation

namespace Sun28.QualitativeRows
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.PreparedPoles
open Sun28.RealPoleBounds Sun28.ScalarHeight Sun28.Scalar Sun28.WitnessIndices Sun28.ContactFactors
open Sun28.RealRatio Sun28.ScalarPlaces Sun28.GaussianSelection Sun28.FiniteWitness Sun28.ContactSieve
open Sun28.Exceptional ManuscriptV15.Arithmetic
noncomputable section

/-- A real window can be fixed separately for every integer, before choosing any primes. -/
structure Window (X : ℤ) where
  c : ℤ
  q : ℤ
  n : Fin 4→ℤ
  C : ℝ
  early : (stepMod (integerRadicand X) fixedMultiplier:ℤ)∣c
  roots : AdmissibleRoots X c q n
  one : 1≤C
  progression : ∀ η : ℚ, slopeThreshold (fixedScale n) C (1/2) < η →
    ∀ (h₀ : ℤ) (L : ℕ), 0<L →
    ∃ (h : ℤ) (k : ℕ) (B : Fin 9→AffineInput),
      h=h₀+(L:ℤ)*k ∧
      let w:=(nineAffine B).doubles
      Consequences w fixedMultiplier anchor ⟨q,h,n,fun i=>h*n i⟩ ∧
      coordinateProduct n=rootProduct w fixedMultiplier ∧
      (∀ i,|scalarEntries w fixedMultiplier i|≤1) ∧
      ∀ j,RealPole w fixedMultiplier anchor (beta X) ((pointScale w fixedMultiplier j)^2) η (1/2)

theorem exists_window {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit) (X : ℤ) :
    Nonempty (Window X) := by
  have mp : 0<fixedMultiplier := by have := fixed_multiplier_spec.2.1; omega
  obtain ⟨dp,mdiv,_⟩ := step_spec (integerRadicand X) mp
  obtain ⟨c,q,n,C,dc,cl,cq,first,shift,odds,luc,one,windows⟩ :=
    integer_three_pole_windows orbit model X anchor fixedMultiplier _ mp fixed_multiplier_spec.1
      dp mdiv 0 (1/2) (by norm_num)
  refine ⟨⟨c,q,n,C,dc,⟨by simpa using cl,cq,first,shift,odds,luc⟩,one,?_⟩⟩
  intro η large h₀ L lp
  obtain ⟨h,k,B,hk,_,_,rep,prod,entries,_,_,real⟩ :=
    windows η large h₀ L lp ∅ Set.finite_empty 0
  exact ⟨h,k,B,hk,rep,prod,entries,real⟩

def fixedWindow {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit) (X : ℤ) :
    Window X := Classical.choice (exists_window orbit model X)

/-- One integer pair, in one window. The only prime size test is the one needed
for the local computations; no density, arbitrary cutoffs, or arbitrarily narrow boxes. -/
def AdmitsRow {X : ℤ} (w : Window X) : Prop :=
  let A:=fixedScale w.n
  ∃ (u v : ℕ) (values : PrimeValues A u v) (π : ↥(shifts A)→Gaussian),
    0<v ∧ requiredDivisor A∣v ∧ slopeThreshold A w.C (1/2)<(slope A u v:ℝ) ∧
    (∀ d∈shifts A,65<values.value d) ∧
    (∀ j,∀ p∈selected values j,¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0) ∧
    NormRays A values π ∧ BalancedOrders π (integerRadicand X)

/-- Each arithmetic query is determined from the actual integer and the earlier real theorem. -/
def FixedWindowRows {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit) : Prop :=
  ∀ X : ℤ, AdmitsRow (fixedWindow orbit model X)

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.exists_window
#print axioms Sun28.QualitativeRows.fixedWindow
