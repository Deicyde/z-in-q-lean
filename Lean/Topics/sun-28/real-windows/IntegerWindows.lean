import RealLucasRoots

/-! One integer input produces the four root indices before the prime choices,
then one h and nine doubled rational affine preimages in every CRT progression. -/
namespace Sun28.RealWindows
open ZInQ ZInQ.Mult ZInQ.AlphaPower Set NumberField Sun28.RealRatio Sun28.Scalar Sun28.Ordinary
open Sun28.Forward Sun28.FixedPreparation Sun28.WitnessIndices
noncomputable section

private theorem roots_at_step {c : ℤ} (pos : 0<c) (six : (6:ℤ)∣c) :
    ∃ t z : ℤ, 0<t ∧ 0<z ∧ Odd t ∧ Odd z ∧ lucas (c+1) t z=0 := by
  obtain ⟨v,hv⟩:=six
  let k := (v-1).toNat
  have v0 : 0≤v-1 := by omega
  have kk : (k:ℤ)=v-1 := Int.toNat_of_nonneg v0
  have s : ((6*k+7:ℕ):ℤ)=c+1 := by push_cast;omega
  have roots:=short_lucas_roots k
  dsimp only at roots
  rw [s] at roots
  exact ⟨_,_,roots⟩

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalAddGroup G]

/-- Sun §6 at an arbitrary input X∈ℤ. The four positive odd roots and the
ordinary real bound precede all choices of slope, prime sizes and CRT moduli. -/
theorem integer_affine_windows (a : Orbit G) (model : ParameterModel a) (X anchor : ℤ)
    (M D : ℕ) (positive : 0<M) (six : 6∣M) (dpos : 0<D) (dil : M∣D) (cmin : ℤ) :
    ∃ (c q : ℤ) (n : Fin 4→ℤ) (C : ℝ), (D:ℤ)∣c ∧ max cmin 0<c ∧ c=(M:ℤ)*q ∧
      n 0=2*X^2+3 ∧ n 1=c+1 ∧ (∀ i,0<n i ∧ Odd (n i)) ∧ lucas (n 1) (n 2) (n 3)=0 ∧ 1≤C ∧
      ∀ (h₀ : ℤ) (L : ℕ),0<L → ∀ (bad : Set ℤ),bad.Finite → ∀ hmin : ℤ,
      ∃ (h : ℤ) (k : ℕ) (A : Fin 9→AffineInput),
        h=h₀+(L:ℤ)*k ∧ max (max anchor hmin) 0<h ∧ h∉bad ∧
        let w:=(nineAffine A).doubles
        Consequences w M anchor ⟨q,h,n,fun i=>h*n i⟩ ∧
        coordinateProduct n=rootProduct w M ∧
        (∀ i,|scalarEntries w M i|≤1) ∧
        (truncAt w.H≠0 ∧ conjugation (truncAt (translatedBase w anchor))≠0) ∧
        (∀ i,∀ σ : K0 →+* ℝ, |σ (ordinaryAt w M anchor (2*(X:ℚ)^2+3) i)|≤C) ∧
        ∀ i,∀ ν : InfinitePlace K0, ν (ordinaryAt w M anchor (2*(X:ℚ)^2+3) i)≤C := by
  obtain ⟨c,q,dc,cpos,cq,select⟩:=choose_affine_windows a model anchor M D positive six dpos dil cmin
  have mo : (6:ℤ)∣(M:ℤ) := by exact_mod_cast six
  have sixc : (6:ℤ)∣c := cq ▸ dvd_mul_of_dvd_left mo q
  obtain ⟨t,z,tp,zp,to',zo,sol⟩:=roots_at_step (by omega) sixc
  let n : Fin 4→ℤ := ![2*X^2+3,c+1,t,z]
  have odds (i : Fin 4) : 0<n i ∧ Odd (n i) := by
    fin_cases i
    · change 0<2*X^2+3 ∧ Odd (2*X^2+3)
      exact ⟨by positivity,⟨X^2+1,by ring⟩⟩
    · change 0<c+1 ∧ Odd (c+1)
      obtain ⟨v,hv⟩:=sixc
      exact ⟨by omega,⟨3*v,by omega⟩⟩
    · exact ⟨tp,to'⟩
    · exact ⟨zp,zo⟩
  obtain ⟨C,one,choose⟩:=select n (2*(X:ℚ)^2+3) (by change c+1-1=c;ring) (fun i=>(odds i).2)
  refine ⟨c,q,n,C,dc,cpos,cq,rfl,rfl,odds,sol,one,?_⟩
  intro h₀ L lp bad fb hm
  obtain ⟨h,k,A,e,hl,out,rep,bounds⟩:=choose h₀ L lp bad fb hm
  exact ⟨h,k,A,e,hl,out,rep,rootProduct_eq rep.represented,bounds⟩

end
end Sun28.RealWindows
#print axioms Sun28.RealWindows.integer_affine_windows
