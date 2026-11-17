import RealTruncation

/-! One positive scalar window, followed by a uniform bound for a finite family
chosen only after the scalar index is fixed, on every subsequent progression. -/
namespace Sun28.RealWindows
open Set Filter ZInQ Sun28.RealRatio Sun28.Scalar
open scoped Topology
noncomputable section
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

/-- Simultaneously positive representatives, strictly past a fixed signed translate. -/
theorem component_centers (a : Orbit G) (anchor : ℤ) :
    ∃ center : Fin a.q → ℤ, (∀ i,max anchor 0 < center i) ∧
      ∀ h₀ : ℤ, ∃ i,center i • a.generator - h₀ • a.generator ∈ a.H := by
  let k := max anchor 0+1
  let f (i : Fin a.q) : ℤ := k*(a.q:ℤ)+((i.val:ℤ)+1)
  have qge : (1:ℤ)≤(a.q:ℤ) := by exact_mod_cast a.positive
  have kg : 0≤k := by dsimp [k];omega
  have grow : k≤k*(a.q:ℤ) := by simpa using mul_le_mul_of_nonneg_left qge kg
  refine ⟨f,?_,?_⟩
  · intro i
    dsimp [f]
    dsimp [k] at grow
    dsimp [k]
    omega
  · intro h₀
    obtain ⟨i,mem⟩:=a.representative h₀
    refine ⟨i,?_⟩
    have step := a.H.zsmul_mem a.step k
    dsimp [f]
    rw [add_zsmul,mul_smul,add_sub_assoc]
    exact a.H.add_mem step mem

variable [CompactSpace G] [IsTopologicalAddGroup G]

/-- The readouts and their bound can depend on c and arbitrary subsequently
fixed roots. The bound precedes the congruence offset, step and finite exclusions. -/
theorem finite_windows (a : Orbit G) (model : ParameterModel a) (anchor : ℤ) :
    ∃ d : ℝ,0<d ∧
    ∀ (D : ℕ),0<D → ∀ cmin : ℤ,∃ (c : ℤ) (u : ℕ),
      c=(D:ℤ)*u ∧ max cmin 0<c ∧
      (∀ σ : K0 →+* ℝ, abs (σ (zAt c)) < d) ∧
      ∀ {I : Type} [Fintype I] [Nonempty I] (F : I→G→ℝ),
      (∀ (i : I) (m : ℤ), max anchor 0 < m → ContinuousAt (F i) (m • a.generator)) →
      ∃ C : ℝ,1≤C ∧
      ∀ (h₀ : ℤ) (L : ℕ),0<L → ∀ (bad : Set ℤ),bad.Finite → ∀ hmin : ℤ,
      ∃ (h : ℤ) (k : ℕ),h=h₀+(L:ℤ)*k ∧ max (max anchor hmin) 0<h ∧ h∉bad ∧
        (∀ σ : K0 →+* ℝ, |σ (zAt c)| < |σ (zAt h)|) ∧
        ∀ i, abs (F i (h • a.generator)) < C := by
  classical
  obtain ⟨j,jpos,covers⟩:=component_centers a anchor
  have : Nonempty (Fin a.q) := ⟨⟨0,a.positive⟩⟩
  let point (i : Fin a.q) := j i • a.generator
  let width (v : Fin a.q × Bool) : ℝ := |parameterAt model (place v.2) (point v.1)|/2
  let d := Finset.univ.inf' Finset.univ_nonempty width
  have jlive (i : Fin a.q) : j i≠0 := by have := jpos i;omega
  have widthpos (v : Fin a.q × Bool) : 0 < width v := by
    dsimp [width,point]
    rw [parameterAt_multiple]
    exact div_pos (abs_pos.mpr (zAt_ne (jlive _) _)) (by norm_num)
  have dp : 0<d := (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun i _=>widthpos i
  refine ⟨d,dp,?_⟩
  intro D dpD cmin
  have small : {x : G | ∀ s, |parameterAt model (place s) x| < d} ∈ 𝓝 (0:G) := by
    apply Filter.eventually_all.mpr
    intro s
    have val : parameterAt model (place s) (0:G)=0 := by
      simpa [zAt,parameter] using parameterAt_multiple model (place s) 0
    have ct := parameterAt_continuousAt model (place s) (0:ℤ)
    simp only [zero_smul] at ct
    exact ct.abs.tendsto (Iio_mem_nhds (by simpa [val] using dp))
  obtain ⟨U,ins,op,mem⟩:=mem_nhds_iff.mp small
  obtain ⟨c,u,eq,high,_,nic⟩:=progression_avoid a.generator a.dense a.H a.divide 0 D dpD
    (show (0:G)-(0:ℤ) • a.generator∈a.H by simp) op mem Set.finite_empty (max cmin 0)
  have sc (σ : K0 →+* ℝ) : |σ (zAt c)| < d := by
    obtain rfl|rfl:=embedding_cases σ
    · simpa [parameterAt_multiple,place] using ins nic false
    · simpa [parameterAt_multiple,place] using ins nic true
  refine ⟨c,u, by simpa using eq,high,sc,?_⟩
  intro I inst inhabited F fc
  let lim (v : Fin a.q × I) : ℝ := |F v.2 (point v.1)|+1
  let C := Finset.univ.sup' Finset.univ_nonempty lim
  have lower (i : Fin a.q) (r : I) : |F r (point i)|+1≤C :=
    Finset.le_sup' lim (Finset.mem_univ (i,r))
  have Cge : 1≤C := by
    have b := lower (Classical.choice ‹Nonempty (Fin a.q)›) (Classical.choice ‹Nonempty I›)
    linarith [abs_nonneg (F (Classical.choice ‹Nonempty I›) (point (Classical.choice ‹Nonempty (Fin a.q)›)))]
  refine ⟨C,Cge,?_⟩
  intro h₀ L posL bad fb hmin
  obtain ⟨i,component⟩:=covers h₀
  have large : {x : G | ∀ s,d < |parameterAt model (place s) x|}∈𝓝 (point i) := by
    apply Filter.eventually_all.mpr
    intro s
    have p := widthpos (i,s)
    have ub:=Finset.inf'_le width (Finset.mem_univ (i,s))
    change 0 < |parameterAt model (place s) (point i)|/2 at p
    change d ≤ |parameterAt model (place s) (point i)|/2 at ub
    exact (parameterAt_continuousAt model (place s) (j i)).abs.tendsto (Ioi_mem_nhds (by linarith))
  have bounded : {x : G | ∀ r,|F r x| < C}∈𝓝 (point i) := by
    apply Filter.eventually_all.mpr
    intro r
    exact (fc r _ (jpos i)).abs.tendsto (Iio_mem_nhds (by linarith [lower i r]))
  obtain ⟨V,iv,vo,vi⟩:=mem_nhds_iff.mp (inter_mem large bounded)
  obtain ⟨h,k,he,hb,out,nice⟩:=progression_avoid a.generator a.dense a.H a.divide h₀ L posL component
    vo vi fb (max (max anchor hmin) 0)
  refine ⟨h,k,he,hb,out,?_,(iv nice).2⟩
  intro σ
  apply (sc σ).trans
  obtain rfl|rfl:=embedding_cases σ
  · simpa [parameterAt_multiple,place] using (iv nice).1 false
  · simpa [parameterAt_multiple,place] using (iv nice).1 true

end
end Sun28.RealWindows
#print axioms Sun28.RealWindows.component_centers
#print axioms Sun28.RealWindows.finite_windows
