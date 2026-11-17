import SelectedReductionCounts
import OrderLcms
import LocalSelection

/-! The selected ordinary trace input in LocalEstimates for the very same
comparison index chosen by the Gaussian order CRT. -/
namespace Sun28.SelectedTrace
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open Sun28.ContactFactors Sun28.ScalarHeight Sun28.FixedPreparation Sun28.GaussianSelection ManuscriptV15.Arithmetic
noncomputable section

/-- Each CRT modulus is an lcm, so the corresponding adjacent norm divides
the correct integer h or h−576!. -/
theorem gaussian_crt_divides {ι : Type*} [Fintype ι] (π : ι→Gaussian) (o : Orders)
    (lp : o.plusOrder=orderLcm π true) (lm : o.minusOrder=orderLcm π false)
    {h : ℤ} (crt : o.accepts h) (i : ι) :
    (adjacentNorm (π i) true:ℤ)∣h ∧ (adjacentNorm (π i) false:ℤ)∣(h-anchor) := by
  have dp : adjacentNorm (π i) true ∣ o.plusOrder := lp ▸ Finset.dvd_lcm (Finset.mem_univ i)
  have dm : adjacentNorm (π i) false ∣ o.minusOrder := lm ▸ Finset.dvd_lcm (Finset.mem_univ i)
  have plus : (o.plusOrder:ℤ)∣h := Int.modEq_zero_iff_dvd.mp crt.plus
  have minus : (o.minusOrder:ℤ)∣h-anchor := Int.modEq_iff_dvd.mp crt.minus.symm
  exact ⟨(Int.natCast_dvd_natCast.mpr dp).trans plus,(Int.natCast_dvd_natCast.mpr dm).trans minus⟩

/-- Uniformly in all three detectors and selected prime occurrences. The input
on CM is the unordered pair of the two actual finite-field cardinalities.
Choosing the opposite square root reverses the cardinalities if necessary. -/
theorem selected_trace_orders {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (one : A 0=1) (alive : ∀ j,A j≠0) (vp : 0<v) (π : ↥(shifts A)→Gaussian) (o : Orders)
    (lp : o.plusOrder=orderLcm π true) (lm : o.minusOrder=orderLcm π false)
    (large : ∀ d∈shifts A,65<values.value d)
    (exclude : ∀ j, ∀ p∈selected values j, ¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0)
    (counts : ∀ d : ↥(shifts A), let p:=values.value d
      ∃ r : ZMod p,r^2=2 ∧
        ((pointCount p (-(3-r)^2)=adjacentNorm (π d) true ∧
          pointCount p (-(3+r)^2)=adjacentNorm (π d) false) ∨
         (pointCount p (-(3-r)^2)=adjacentNorm (π d) false ∧
          pointCount p (-(3+r)^2)=adjacentNorm (π d) true)))
    {X q h : ℤ} {n : Fin 4→ℤ} {points : NinePoints}
    (crt : o.accepts h) (represented : Consequences points fixedMultiplier anchor ⟨q,h,n,fun i=>h*n i⟩)
    (root : lucas (n 1) (n 2) (n 3)=0) (firstRoot : beta X=(n 0:ℚ)) :
    ∀ j, let t:=argument A u v j
      let T:=ordinaryTraceAt points fixedMultiplier anchor (beta X) (A j) t
      ∀ p∈selected values j, T≠0 ∧ padicValRat p T=0 ∧ padicValRat p (detector (A j) t/T^2)=1 := by
  intro j
  dsimp only
  intro p sel
  obtain ⟨a,ha,eq⟩:=Finset.mem_image.mp sel
  let d : ↥(shifts A):=⟨-a/A j,shift_mem A j ha⟩
  have e : values.value d=p := eq
  obtain ⟨r,hr,both⟩ := (e ▸ counts d : ∃ r : ZMod p,r^2=2 ∧ _)
  let _ := Fact.mk (selected_prime values sel)
  obtain ⟨off,sep,unit⟩:=exclude j p sel
  have big : 65<p := e ▸ large d d.property
  obtain ⟨dp,dm⟩:=gaussian_crt_divides π o lp lm crt d
  have finish {s : ZMod p} (hs : s^2=2) (l : pointCount p (-(3-s)^2)=adjacentNorm (π d) true)
      (m : pointCount p (-(3+s)^2)=adjacentNorm (π d) false) :=
    selected_shift_pole_of_counts values one vp (alive j) sel big off sep unit hs represented
      (beta X) root firstRoot (l ▸ dp) (m ▸ dm)
  rcases both with ⟨l,m⟩|⟨l,m⟩
  · exact finish hr l m
  · exact finish (s:= -r) (by rw [neg_sq,hr]) (by simpa using m)
      (by simpa only [← sub_eq_add_neg] using l)

end
end Sun28.SelectedTrace
#print axioms Sun28.SelectedTrace.gaussian_crt_divides
#print axioms Sun28.SelectedTrace.selected_trace_orders
