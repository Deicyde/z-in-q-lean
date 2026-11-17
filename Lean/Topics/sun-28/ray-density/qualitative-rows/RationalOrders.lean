import SingleWindow
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace Sun28.QualitativeRows
open ZInQ Sun28.ContactFactors Sun28.ScalarPlaces Sun28.FixedPreparation Sun28.TwistRank
open Sun28.SelectedTrace Sun28.Scalar Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices Sun28.ScalarHeight
noncomputable section
open private mod_pos fixed_compatible from ActualOrders

theorem solve_at_orders {ι : Type*} [Fintype ι] (orders : ι → Bool → ℕ) (r : ℤ)
    (nz : ∀ i s, 0<orders i s)
    (clear : ∀ v, ¬Walk (Edge orders (fixedMod r) (fixedRes r) (Nat.factorial 576)) v v true) :
    ∃ (flip : ι → Bool) (h₀ : ℤ) (L : ℕ), 0<L ∧ ∀ k : ℤ,
      let h := h₀+(L:ℤ)*k
      ((kernelMod r : ℕ) : ℤ) ∣ h ∧
      (∀ p∈supportPlaces r, h ≡ (p:ℤ)^comparisonDepth r p [ZMOD (p:ℤ)^(comparisonDepth r p+1)]) ∧
      ∀ i, (orders i (flip i):ℤ) ∣ h ∧ (orders i (!(flip i)):ℤ) ∣ (h-anchor) := by
  obtain ⟨x,h,L,pos,all⟩ := (graph_criterion orders
    (fixedMod r) (fixedRes r) (Nat.factorial 576) nz (mod_pos r) (fixed_compatible r)).mp clear
  refine ⟨x,h,L,pos,fun k => ⟨Int.modEq_zero_iff_dvd.mp (all k (.inl none)),?_,?_⟩⟩
  · intro p mem
    simpa only [comparisonMod,comparisonRes,fixedMod,fixedRes,Nat.cast_pow] using
      all k (.inl (some ⟨p,mem⟩))
  · intro i
    have a := all k (.inr (i,x i))
    have b := all k (.inr (i,!(x i)))
    simp only [comparisonMod,comparisonRes,Bool.xor_self,Bool.false_eq_true,ite_false,Nat.cast_zero] at a
    refine ⟨Int.modEq_zero_iff_dvd.mp a,?_⟩
    apply Int.modEq_iff_dvd.mp
    have flip : (!(x i) ^^ x i)=true := by cases x i <;> rfl
    simpa only [comparisonMod,comparisonRes,flip,ite_true,anchor] using b.symm


/-- The two counts can be computed from a rational prime without finding any
Gaussian generator. True is the first reduced curve for the chosen root. -/
def curveOrders {p : ℕ} (z : ZMod p) (side : Bool) : ℕ :=
  pointCount p (-(3-(if side then z else -z))^2)

/-- The rational shape class puts a square root of two in the prime field. -/
theorem exists_root {p : ℕ} [Fact p.Prime] (size : 65<p) (residue : p%16=1) :
    ∃ z : ZMod p, z^2=2 := by
  obtain ⟨z,h⟩ := (ZMod.exists_sq_eq_two_iff (p:=p) (by omega)).mpr
    (Or.inl (by omega : p%8=1))
  exact ⟨z, by simpa only [pow_two] using h.symm⟩

/-- Trace success in the rational test, using opposite square roots at each
prime when required by the common integer progression. -/
theorem rational_trace {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (one : A 0=1) (alive : ∀ j,A j≠0) (vp : 0<v)
    (z : (i : ↥(shifts A))→ZMod (values.value i)) (sq : ∀ i,(z i)^2=2)
    (flip : ↥(shifts A)→Bool) (large : ∀ d∈shifts A,65<values.value d)
    (exclude : ∀ j, ∀ p∈selected values j, ¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0)
    {X q h : ℤ} {n : Fin 4→ℤ} {points : NinePoints}
    (orders : ∀ i, (curveOrders (z i) (flip i):ℤ)∣h ∧ (curveOrders (z i) (!(flip i)):ℤ)∣(h-anchor))
    (represented : Consequences points fixedMultiplier anchor ⟨q,h,n,fun i=>h*n i⟩)
    (root : lucas (n 1) (n 2) (n 3)=0) (firstRoot : beta X=(n 0:ℚ)) :
    ∀ j, let t:=argument A u v j
      let T:=ordinaryTraceAt points fixedMultiplier anchor (beta X) (A j) t
      ∀ p∈selected values j, T≠0 ∧ padicValRat p T=0 ∧ padicValRat p (detector (A j) t/T^2)=1 := by
  intro j
  dsimp only
  intro p sel
  obtain ⟨a,ha,e⟩:=Finset.mem_image.mp sel
  let d : ↥(shifts A) := ⟨-a/A j,shift_mem A j ha⟩
  have eq : values.value d=p := e
  subst p
  let _ := Fact.mk (values.prime _ d.property)
  obtain ⟨off,sep,unit⟩:=exclude j _ sel
  obtain ⟨left,right⟩:=orders d
  let r:=if flip d then z d else -(z d)
  have hs : r^2=2 := by dsimp [r];split <;> simp [sq]
  apply selected_shift_pole_of_counts values one vp (alive j) sel (large _ d.property) off sep unit
    hs represented (beta X) root firstRoot
  · exact left
  · cases side : flip d <;> simpa [curveOrders,r,side,sub_eq_add_neg] using right

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.solve_at_orders
#print axioms Sun28.QualitativeRows.exists_root
#print axioms Sun28.QualitativeRows.rational_trace
