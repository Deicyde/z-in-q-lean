import GeneratorKernel
import RationalOrders

namespace Sun28.QualitativeRows
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open Sun28.SelectedTrace Sun28.ContactFactors Sun28.ScalarHeight Sun28.FixedPreparation
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

theorem selected_pole_of_period {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (one : A 0=1) (vp : 0<v) {j : Fin 3} (nz : A j≠0) {p : ℕ} [Fact p.Prime]
    (sel : p∈selected values j) (large : 65<p) (off : ¬p∣dilation A) (good : ¬p∣separation)
    (unit : padicValRat p (A j)=0) {r : ZMod p} (hr : r^2=2)
    {points : NinePoints} {M : ℕ} {c q h : ℤ} {n : Fin 4→ℤ}
    (rep : Consequences points M c ⟨q,h,n,fun i=>h*n i⟩)
    (β : ℚ) (root : lucas (n 1) (n 2) (n 3)=0) (first : β=(n 0:ℚ))
    (firstPeriod : (pointPeriod large hr:ℤ)∣h)
    (secondPeriod : (pointPeriod large (by rwa [neg_sq] : (-r)^2=2):ℤ)∣(h-c)) :
    let t:=argument A u v j
    let T:=ordinaryTraceAt points M c β (A j) t
    T≠0 ∧ padicValRat p T=0 ∧ padicValRat p (detector (A j) t/T^2)=1 := by
  obtain ⟨π,hπ,kernel⟩:=exists_prime_residueAt r hr
  have hr' : (-r)^2=2 := by rwa [neg_sq]
  have other:=residueAt_neg_ker hr kernel hr'
  have dvd := (kernel (p:Zs)).mp (by simp)
  let _:=selectedPlace_liesOver hπ dvd
  apply selected_shift_pole values one vp nz sel large off good unit (selectedPlace π hπ)
    rep β root first
  · rw [selectedPlace_order];exact anchor_from_period large hr hπ kernel firstPeriod
  · rw [selectedPlace_conjugate_order];exact anchor_from_period large hr' (prime_star hπ) other secondPeriod

def periodAt {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (big : ∀ d∈shifts A,65<values.value d)
    (z : (i : ↥(shifts A))→ZMod (values.value i)) (sq : ∀ i,(z i)^2=2)
    (i : ↥(shifts A)) (s : Bool) : ℕ := by
  let _ := Fact.mk (values.prime _ i.property)
  exact if s then pointPeriod (big _ i.property) (sq i)
    else pointPeriod (big _ i.property) (by rw [neg_sq,sq] : (-z i)^2=2)

theorem periodAt_positive {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (big : ∀ d∈shifts A,65<values.value d)
    (z : (i : ↥(shifts A))→ZMod (values.value i)) (sq : ∀ i,(z i)^2=2)
    (i : ↥(shifts A)) (s : Bool) : 0<periodAt values big z sq i s := by
  let _ := Fact.mk (values.prime _ i.property)
  cases s <;> apply period_pos

theorem periodAt_dvd {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (big : ∀ d∈shifts A,65<values.value d)
    (z : (i : ↥(shifts A))→ZMod (values.value i)) (sq : ∀ i,(z i)^2=2)
    (i : ↥(shifts A)) (s : Bool) : periodAt values big z sq i s ∣ curveOrders (z i) s := by
  let _ := Fact.mk (values.prime _ i.property)
  cases s <;> apply period_dvd

theorem period_trace {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (one : A 0=1) (alive : ∀ j,A j≠0) (vp : 0<v)
    (z : (i : ↥(shifts A))→ZMod (values.value i)) (sq : ∀ i,(z i)^2=2)
    (flip : ↥(shifts A)→Bool) (large : ∀ d∈shifts A,65<values.value d)
    (exclude : ∀ j, ∀ p∈selected values j, ¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0)
    {X q h : ℤ} {n : Fin 4→ℤ} {points : NinePoints}
    (orders : ∀ i, (periodAt values large z sq i (flip i):ℤ)∣h ∧
      (periodAt values large z sq i (!(flip i)):ℤ)∣(h-anchor))
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
  cases chosen : flip d with
  | true =>
    rw [chosen] at left right
    exact selected_pole_of_period values one vp (alive j) sel (large _ d.property) off sep unit
      (sq d) represented (beta X) root firstRoot left right
  | false =>
    rw [chosen] at left right
    apply selected_pole_of_period values one vp (alive j) sel (large _ d.property) off sep unit
      (r:= -(z d)) (by rw [neg_sq,sq]) represented (beta X) root firstRoot left
    change (pointPeriod (large _ d.property) (sq d):ℤ)∣(h-anchor) at right
    have twice (v : ZMod (values.value d)) (hv : v^2=2) :
        pointPeriod (large _ d.property) (by simp only [neg_neg,hv] : (- -v)^2=2) =
        pointPeriod (large _ d.property) hv := by simp only [neg_neg]
    exact (twice (z d) (sq d)).symm ▸ right

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.selected_pole_of_period
#print axioms Sun28.QualitativeRows.periodAt_positive
#print axioms Sun28.QualitativeRows.periodAt_dvd
#print axioms Sun28.QualitativeRows.period_trace
