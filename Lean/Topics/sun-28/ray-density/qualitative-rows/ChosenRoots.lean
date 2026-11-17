import ActualOrders
import CMPointCounts
import SelectedTraceCRT

namespace Sun28.QualitativeRows
open ZInQ Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open Sun28.ContactFactors Sun28.ScalarHeight Sun28.FixedPreparation Sun28.ContactSieve
open Sun28.SelectedTrace ManuscriptV15.Arithmetic
noncomputable section

/-- Both choices of square root are available at each rational selected prime.
The choice is local to that prime, and works for all its detector occurrences. -/
theorem oriented_trace_orders {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (one : A 0=1) (alive : ∀ j,A j≠0) (vp : 0<v) (π : ↥(shifts A)→Gaussian)
    (rays : NormRays A values π) (flip : ↥(shifts A)→Bool)
    (large : ∀ d∈shifts A,65<values.value d)
    (exclude : ∀ j, ∀ p∈selected values j, ¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0)
    {X q h : ℤ} {n : Fin 4→ℤ} {points : NinePoints}
    (orders : ∀ d, (adjacentNorm (π d) (flip d):ℤ)∣h ∧
      (adjacentNorm (π d) (!(flip d)):ℤ)∣(h-anchor))
    (represented : Consequences points fixedMultiplier anchor ⟨q,h,n,fun i=>h*n i⟩)
    (root : lucas (n 1) (n 2) (n 3)=0) (firstRoot : beta X=(n 0:ℚ)) :
    ∀ j, let t:=argument A u v j
      let T:=ordinaryTraceAt points fixedMultiplier anchor (beta X) (A j) t
      ∀ p∈selected values j, T≠0 ∧ padicValRat p T=0 ∧ padicValRat p (detector (A j) t/T^2)=1 := by
  intro j
  dsimp only
  intro p sel
  obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp sel
  let d : ↥(shifts A) := ⟨-a/A j,shift_mem A j ha⟩
  have e : values.value d=p := eq
  let _ := Fact.mk (selected_prime values sel)
  obtain ⟨r,hr,plus,minus⟩ := CMReduction.exists_oriented_root ((rays.norm d).trans e)
    (rays.ray16 d) (rays.ray7 d)
  obtain ⟨off,sep,unit⟩ := exclude j p sel
  have big : 65<p := e ▸ large d d.property
  obtain ⟨dp,dm⟩ := orders d
  cases chosen : flip d with
  | false =>
    rw [chosen] at dp dm
    apply selected_shift_pole_of_counts values one vp (alive j) sel big off sep unit
      (r:= -r) (by rw [neg_sq,hr]) represented (beta X) root firstRoot
    · rw [sub_neg_eq_add,minus]; exact dp
    · rw [←sub_eq_add_neg,plus]; exact dm
  | true =>
    rw [chosen] at dp dm
    exact selected_shift_pole_of_counts values one vp (alive j) sel big off sep unit hr represented
      (beta X) root firstRoot (plus ▸ dp) (minus ▸ dm)

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.oriented_trace_orders
