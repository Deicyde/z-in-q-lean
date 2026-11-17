import ProgressionRecurrence

/-! Uniform windows on a compact cyclic orbit. Bounds are fixed before the
progression modulus. Finitely many exceptional indices can be chosen afterwards. -/
namespace Sun28.RealRatio
open Set Filter
open scoped Topology
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

/-- Only the following consequences of the compact Lie group structure are used.
The multiple qg is in the divisible subgroup H (the identity component). -/
structure Orbit (G : Type*) [AddCommGroup G] [TopologicalSpace G] where
  generator : G
  dense : DenseRange (fun n : ℤ => n • generator)
  H : AddSubgroup G
  q : ℕ
  positive : 0<q
  step : (q:ℤ) • generator∈H
  divide : ∀ L : ℕ,0<L → ∀ x∈H,∃ y : G,L • y=x

/-- A representative of the component of h₀, chosen from 1,...,q. -/
theorem Orbit.representative (a : Orbit G) (h₀ : ℤ) :
    ∃ i : Fin a.q, (((i.val:ℤ)+1) • a.generator)-h₀ • a.generator∈a.H := by
  have qpos : 0<(a.q:ℤ) := by exact_mod_cast a.positive
  let j := (h₀-1) % (a.q:ℤ)
  have jpos : 0≤j := Int.emod_nonneg _ qpos.ne'
  have jlt : j<(a.q:ℤ) := Int.emod_lt_of_pos _ qpos
  let i : Fin a.q := ⟨j.toNat,by omega⟩
  refine ⟨i,?_⟩
  have eq : ((i.val:ℤ)+1)-h₀ = -((h₀-1)/(a.q:ℤ))*(a.q:ℤ) := by
    have id := Int.emod_add_mul_ediv (h₀-1) (a.q:ℤ)
    change (j.toNat:ℤ)+1-h₀=_
    rw [Int.toNat_of_nonneg jpos]
    dsimp [j]
    rw [neg_mul,mul_comm ((h₀-1)/(a.q:ℤ)) (a.q:ℤ)]
    omega
  rw [sub_eq_add_neg,←sub_zsmul,eq,mul_smul]
  exact a.H.zsmul_mem a.step _

variable [CompactSpace G] [IsTopologicalAddGroup G]

/-- The width depends on the real coordinates and G alone. It is chosen before
the positive modulus D of c, the later signed offset h₀ and modulus L of h,
a finite exceptional set E, and either requested lower bound. -/
theorem uniform_ratio (a : Orbit G) (z : Bool→G→ℝ)
    (at_zero : ∀ s,ContinuousAt (z s) 0) (zero : ∀ s,z s 0=0)
    (at_multiple : ∀ s (j : ℤ), j≠0 → ContinuousAt (z s) (j • a.generator))
    (nonzero : ∀ s (j : ℤ), j≠0 → z s (j • a.generator)≠0) :
    ∃ d : ℝ,0<d ∧
    ∀ (D : ℕ),0<D → ∀ cmin : ℤ,∃ (c : ℤ) (u : ℕ),
      c=(D:ℤ)*u ∧ cmin<c ∧ (∀ s, |z s (c • a.generator)| < d) ∧
      ∀ (h₀ : ℤ) (L : ℕ),0<L → ∀ (E : Set ℤ), E.Finite → ∀ hmin : ℤ,
      ∃ (h : ℤ) (k : ℕ), h=h₀+(L:ℤ)*k ∧ hmin<h ∧ h∉E ∧
        ∀ s, d < |z s (h • a.generator)| := by
  classical
  let : Nonempty (Fin a.q) := ⟨⟨0,a.positive⟩⟩
  let center (i : Fin a.q) := ((i.val:ℤ)+1) • a.generator
  let val (v : Fin a.q × Bool) : ℝ := |z v.2 (center v.1)|/2
  let d := Finset.univ.inf' Finset.univ_nonempty val
  have valpos (v : Fin a.q × Bool) : 0<val v :=
    div_pos (abs_pos.mpr (nonzero _ _ (by positivity))) (by norm_num)
  have dp : 0<d := (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun i _ => valpos i
  refine ⟨d,dp,?_⟩
  intro D posD cmin
  have near0 : {x : G | ∀ s,|z s x| < d} ∈ 𝓝 (0:G) := by
    apply Filter.eventually_all.mpr
    intro s
    have z0 : |z s 0| < d := by simpa [zero] using dp
    exact ((at_zero s).abs).tendsto (Iio_mem_nhds z0)
  obtain ⟨U,inc,opened,inside⟩:=mem_nhds_iff.mp near0
  obtain ⟨c,u,ce,cb,_,cu⟩:=progression_avoid a.generator a.dense a.H a.divide 0 D posD
    (show (0:G)-(0:ℤ) • a.generator∈a.H by simp) opened inside Set.finite_empty cmin
  refine ⟨c,u,by simpa using ce,cb,inc cu,?_⟩
  intro h₀ L posL E fin hmin
  obtain ⟨i,ci⟩:=a.representative h₀
  have nearH : {x : G | ∀ s,d < |z s x|} ∈ 𝓝 (center i) := by
    apply Filter.eventually_all.mpr
    intro s
    have half := Finset.inf'_le val (Finset.mem_univ (i,s))
    have nz:=valpos (i,s)
    change 0 < |z s (center i)|/2 at nz
    change d ≤ |z s (center i)|/2 at half
    have threshold : d < |z s (center i)| := by linarith
    exact ((at_multiple s _ (by positivity)).abs).tendsto (Ioi_mem_nhds threshold)
  obtain ⟨V,incV,openedV,insideV⟩:=mem_nhds_iff.mp nearH
  obtain ⟨h,k,e,b,out,atV⟩:=progression_avoid a.generator a.dense a.H a.divide h₀ L posL ci openedV insideV fin hmin
  exact ⟨h,k,e,b,out,incV atV⟩

end Sun28.RealRatio
#print axioms Sun28.RealRatio.Orbit.representative
#print axioms Sun28.RealRatio.uniform_ratio
