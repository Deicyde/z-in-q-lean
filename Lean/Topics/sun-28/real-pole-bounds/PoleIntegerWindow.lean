import PoleTraceWindow
import IntegerWindows

/-! The three thresholds depend only on the integer roots, and precede the
choice of the common slope, the congruence progression and the nine preimages. -/
namespace Sun28.RealPoleBounds
open Set NumberField ZInQ ZInQ.Mult Sun28.RealRatio Sun28.RealWindows Sun28.Scalar Sun28.Ordinary
open Sun28.Forward Sun28.FixedPreparation Sun28.WitnessIndices
noncomputable section

def fixedScale (n : Fin 4→ℤ) (j : Fin 3) : ℚ :=
  (scaleRoot (coordinateProduct n).re (coordinateProduct n).im j)^2

theorem actual_scales_positive (n : Fin 4→ℤ) (nz : ∀ i,n i≠0) : ∀ j,0<fixedScale n j := by
  have product (σ : K0 →+* ℝ) (deltaBound : 1≤σ delta) : 0<σ (coordinateProduct n) := by
    rw [coordinateProduct,map_prod]
    exact Finset.prod_pos fun i _=>zero_lt_one.trans_le (deltaBound.trans (generator_real_lower σ deltaBound (nz i)))
  have first := product K0.embPlus embPlus_delta_mem.1
  have second := product K0.embMinus embMinus_delta_mem.1
  rw [K0.embPlus_apply] at first
  rw [K0.embMinus_apply] at second
  have rational : 0<(coordinateProduct n).re := by
    exact_mod_cast (by linarith : 0<((coordinateProduct n).re:ℝ))
  intro j
  fin_cases j
  · norm_num [fixedScale,scaleRoot]
  · exact sq_pos_of_pos rational
  · change 0<(1+(coordinateProduct n).im^2)^2
    positivity

def slopeThreshold (scales : Fin 3→ℚ) (C ε : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j=>(depthThreshold (scales j) C ε+3)/(scales j:ℝ))

theorem above_threshold {scales : Fin 3→ℚ} (pos : ∀ j,0<scales j) {C ε : ℝ} {η : ℚ}
    (large : slopeThreshold scales C ε < η) :
    ∀ j,depthThreshold (scales j) C ε < (scales j*η-3:ℚ) := by
  intro j
  have p : 0<(scales j:ℝ):=by exact_mod_cast pos j
  have small : (depthThreshold (scales j) C ε+3)/(scales j:ℝ)<η :=
    (Finset.le_sup' _ (Finset.mem_univ j)).trans_lt large
  have more := (div_lt_iff₀ p).mp small
  push_cast
  linarith

/-- All Archimedean inequalities and denominator guards on one actual ordinary scale. -/
def RealPole (w : NinePoints) (M : ℕ) (anchor : ℤ) (β A η : ℚ) (ε : ℝ) : Prop :=
  let t:=A*η
  let r:=detector A t
  let T:=ordinaryTraceAt w M anchor β A t
  t∉marks ∧ t≠3 ∧ 0<r ∧ productAt r (t-3) (ordinaryAt w M anchor β)≠0 ∧
    0<T ∧ 0<r/T^2 ∧ ((r/T^2:ℚ):ℝ)<ε

theorem three_small_poles (w : NinePoints) (M : ℕ) (anchor : ℤ) (β : ℚ)
    (C ε : ℝ) (ep : 0<ε) (scales : Fin 3→ℚ) (positive : ∀ j,0<scales j)
    (η : ℚ) (large : slopeThreshold scales C ε < η)
    (bounds : ∀ i,∀ σ : K0 →+* ℝ,|σ (ordinaryAt w M anchor β i)|≤C) :
    ∀ j, RealPole w M anchor β (scales j) η ε := by
  intro j
  exact bounded_ordinary_pole w M anchor β _ _ C ε (positive j) ep (above_threshold positive large j) bounds

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalAddGroup G]

/-- One rational slope threshold at all three fixed root scales, issued before
the arbitrary progression and its actual common comparison point. -/
theorem integer_three_pole_windows (a : Orbit G) (model : ParameterModel a) (X anchor : ℤ)
    (M D : ℕ) (positive : 0<M) (six : 6∣M) (dpos : 0<D) (dil : M∣D) (cmin : ℤ) (ε : ℝ) (ep : 0<ε) :
    ∃ (c q : ℤ) (n : Fin 4→ℤ) (C : ℝ), (D:ℤ)∣c ∧ max cmin 0<c ∧ c=(M:ℤ)*q ∧
      n 0=2*X^2+3 ∧ n 1=c+1 ∧ (∀ i,0<n i ∧ Odd (n i)) ∧ lucas (n 1) (n 2) (n 3)=0 ∧ 1≤C ∧
      ∀ η : ℚ,slopeThreshold (fixedScale n) C ε < η →
      ∀ (h₀ : ℤ) (L : ℕ),0<L → ∀ (bad : Set ℤ),bad.Finite → ∀ hmin : ℤ,
      ∃ (h : ℤ) (k : ℕ) (B : Fin 9→AffineInput),
        h=h₀+(L:ℤ)*k ∧ max (max anchor hmin) 0<h ∧ h∉bad ∧
        let w:=(nineAffine B).doubles
        Consequences w M anchor ⟨q,h,n,fun i=>h*n i⟩ ∧ coordinateProduct n=rootProduct w M ∧
        (∀ i,|scalarEntries w M i|≤1) ∧
        (truncAt w.H≠0 ∧ conjugation (truncAt (translatedBase w anchor))≠0) ∧
        (∀ i,∀ σ : K0 →+* ℝ, |σ (ordinaryAt w M anchor (2*(X:ℚ)^2+3) i)|≤C) ∧
        ∀ j,RealPole w M anchor (2*(X:ℚ)^2+3) ((pointScale w M j)^2) η ε := by
  obtain ⟨c,q,n,C,div,cp,cq,nβ,ns,odd,luc,one,give⟩:=
    integer_affine_windows a model X anchor M D positive six dpos dil cmin
  refine ⟨c,q,n,C,div,cp,cq,nβ,ns,odd,luc,one,?_⟩
  intro η ηbig h₀ L lp bad fb hm
  obtain ⟨h,k,B,eq,late,out,rep,prod,entries,live,bound,_⟩:=give h₀ L lp bad fb hm
  refine ⟨h,k,B,eq,late,out,rep,prod,entries,live,bound,?_⟩
  intro j
  have points:=three_small_poles _ _ _ _ C ε ep (fixedScale n) (actual_scales_positive n (fun i=>(odd i).1.ne')) η ηbig bound j
  simpa only [fixedScale,pointScale,prod] using points


/-- The literal one-half in the fixed pole criterion, with all three actual point scales. -/
theorem three_poles_half (w : NinePoints) (M : ℕ) (anchor : ℤ) (β : ℚ) (C : ℝ)
    (n : Fin 4→ℤ) (nz : ∀ i,n i≠0) (prod : coordinateProduct n=rootProduct w M)
    (η : ℚ) (large : slopeThreshold (fixedScale n) C (1/2) < η)
    (bounds : ∀ i,∀ σ : K0 →+* ℝ,|σ (ordinaryAt w M anchor β i)|≤C) :
    ∀ j, let A := (pointScale w M j)^2
      let t:=A*η
      let T:=ordinaryTraceAt w M anchor β A t
      T≠0 ∧ 0<detector A t/T^2 ∧ detector A t/T^2 < 1/2 := by
  intro j
  have h:=three_small_poles w M anchor β C (1/2) (by norm_num) _ (actual_scales_positive n nz) η large bounds j
  simp only [RealPole,fixedScale,pointScale,prod] at h ⊢
  refine ⟨h.2.2.2.2.1.ne',h.2.2.2.2.2.1,?_⟩
  apply (Rat.cast_lt (K:=ℝ)).mp
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow] using h.2.2.2.2.2.2

end
end Sun28.RealPoleBounds
#print axioms Sun28.RealPoleBounds.actual_scales_positive
#print axioms Sun28.RealPoleBounds.above_threshold
#print axioms Sun28.RealPoleBounds.three_small_poles
#print axioms Sun28.RealPoleBounds.integer_three_pole_windows
#print axioms Sun28.RealPoleBounds.three_poles_half
