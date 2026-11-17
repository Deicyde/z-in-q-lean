import CompactWindows
import RealEntries
import DyadicTruncation

/-! The same positive integer H controls both real embeddings on every signed
progression. The only local real-model data are continuity and coordinate evaluation. -/
namespace Sun28.RealRatio
open Set Filter NumberField ZInQ Sun28.Scalar Sun28.FixedPreparation Sun28.WitnessIndices Sun28.Forward
open scoped Topology
noncomputable section

def zAt (m : ℤ) := parameter (m • paperGenerator sqrt2_sq)

def place : Bool → (K0 →+* ℝ) | false => K0.embPlus | true => K0.embMinus

/-- The two named maps exhaust all real embeddings, with their signs. -/
theorem embedding_cases (σ : K0 →+* ℝ) : σ=K0.embPlus ∨ σ=K0.embMinus := by
  have sq : (σ sqrt2)^2=2 := by rw [←map_pow,sqrt2_sq,map_ofNat]
  have rt := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have prod : (σ sqrt2-Real.sqrt 2)*(σ sqrt2+Real.sqrt 2)=0 := by nlinarith only [sq,rt]
  have formula (x : K0) : σ x = (x.re:ℝ)+(x.im:ℝ)*σ sqrt2 := by
    calc
      σ x = σ ((x.re:K0)+(x.im:K0)*sqrt2) := congrArg σ (K0.eq_re_add_im_mul_sqrt2 x)
      _ = _ := by simp
  rcases mul_eq_zero.mp prod with p|n
  · left
    ext x
    rw [formula,K0.embPlus_apply,sub_eq_zero.mp p]
  · right
    ext x
    rw [formula,K0.embMinus_apply,show σ sqrt2= -Real.sqrt 2 by linarith only [n]]
    ring

/-- For every nonzero signed index, injectivity of each field embedding transfers
the checked dyadic nonvanishing to the two real parameter values. -/
theorem zAt_ne {m : ℤ} (nz : m≠0) (σ : K0 →+* ℝ) : σ (zAt m)≠0 := by
  simpa only [zAt,map_zero] using σ.injective.ne ((dyadic_parameter m nz).2)

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
/-- To instantiate this structure use the compact closure of the diagonal real
orbit. The finite component quotient data belong to Orbit. No ratio or
progression conclusion is an assumption of the adapter. -/
structure ParameterModel (a : Orbit G) where
  z : Bool→G→ℝ
  value : ∀ (s : Bool) (m : ℤ), z s (m • a.generator) = place s (zAt m)
  zero_continuous : ∀ s, ContinuousAt (z s) 0
  affine_continuous : ∀ s (m : ℤ), m≠0 → ContinuousAt (z s) (m • a.generator)

variable [CompactSpace G] [IsTopologicalAddGroup G]

/-- One unrestricted signed arithmetic progression for H, chosen only after
the positive scalar step c is chosen. All infinite places hold simultaneously.
An arbitrary finite exceptional set of signed indices is allowed. -/
theorem choose_real_indices (a : Orbit G) (model : ParameterModel a) :
    ∃ d : ℝ,0<d ∧
    ∀ (D : ℕ),0<D → ∀ cmin : ℤ,∃ (c : ℤ) (u : ℕ),
      c=(D:ℤ)*u ∧ max cmin 0<c ∧
      (∀ σ : K0 →+* ℝ, |σ (zAt c)| < d) ∧
      ∀ (h₀ : ℤ) (L : ℕ),0<L → ∀ (bad : Set ℤ),bad.Finite → ∀ hmin : ℤ,
      ∃ (h : ℤ) (k : ℕ), h=h₀+(L:ℤ)*k ∧ max hmin 0<h ∧ h∉bad ∧
        (∀ σ : K0 →+* ℝ, |σ (zAt c)| < |σ (zAt h)|) ∧
        ∀ ν : InfinitePlace K0, ν (zAt c)<ν (zAt h) := by
  classical
  have z0 (s : Bool) : model.z s 0=0 := by
    simpa [zAt,parameter] using model.value s 0
  have zn (s : Bool) (m : ℤ) (hm : m≠0) : model.z s (m • a.generator)≠0 := by
    rw [model.value];exact zAt_ne hm _
  obtain ⟨d,dp,choice⟩:=uniform_ratio a model.z model.zero_continuous z0 model.affine_continuous zn
  refine ⟨d,dp,?_⟩
  intro D hD cm
  obtain ⟨c,u,ce,cb,small,rest⟩:=choice D hD (max cm 0)
  have sc (σ : K0 →+* ℝ) : |σ (zAt c)| < d := by
    rcases embedding_cases σ with rfl|rfl
    · simpa [model.value,place] using small false
    · simpa [model.value,place] using small true
  refine ⟨c,u,ce,cb,sc,?_⟩
  intro h₀ L hl bad fb hm
  obtain ⟨h,k,he,hb,hout,high⟩:=rest h₀ L hl bad fb (max hm 0)
  have real (σ : K0 →+* ℝ) : |σ (zAt c)| < |σ (zAt h)| := by
    apply (sc σ).trans
    rcases embedding_cases σ with rfl|rfl
    · simpa [model.value,place] using high false
    · simpa [model.value,place] using high true
  refine ⟨h,k,he,hb,hout,real,?_⟩
  intro ν
  have mem : ν∈(Finset.univ : Finset (InfinitePlace K0)) := Finset.mem_univ _
  rw [infinitePlace_K0.1] at mem
  rcases Finset.mem_insert.mp mem with rfl|p
  · simpa only [wPlus_apply] using real K0.embPlus
  · have := Finset.mem_singleton.mp p
    subst ν
    simpa only [wMinus_apply] using real K0.embMinus

omit [CompactSpace G] [IsTopologicalAddGroup G] in
/-- Membership of finitely many exceptional point values at finitely many
signed translates can exclude only finitely many integer indices. -/
theorem paper_translates_finite {I : Type*} [Finite I] (s c : I → ℤ)
    (ns : ∀ i,s i≠0) (bad : I→Set CPoint) (fb : ∀ i,(bad i).Finite) :
    (⋃ i, (fun h : ℤ => (s i*(h-c i)) • P) ⁻¹' bad i).Finite := by
  apply finite_bad_indices _ _ _ fb
  intro i x y e
  have m := index_injective e
  have v := mul_left_cancel₀ (ns i) m
  omega

/-- One H satisfying the real inequalities gives all six entries a common
absolute bound of one for the actual represented nine-point inputs. -/
theorem entries_on_shared_indices {w : NinePoints} {M : ℕ} {anchor : ℤ} {l : Labels}
    (rep : Consequences w M anchor l) {c h : ℤ} (cvalue : l.n 1-1=c) (hvalue : l.h=h)
    (less : ∀ σ : K0 →+* ℝ, |σ (zAt c)| < |σ (zAt h)|) :
    ∀ i, |scalarEntries w M i|≤1 := by
  apply real_entries rep
  intro σ _
  have sc : scalarEquiv (scalarPoint w M)=c • paperGenerator sqrt2_sq := by
    rw [← rep.scalar_point,scalar_index,cvalue]
  have hpoint : scalarEquiv w.H=h • paperGenerator sqrt2_sq := by
    rw [←rep.represented.h_point,scalar_index,hvalue]
  rw [sc,hpoint]
  exact (less σ).le

end
end Sun28.RealRatio
#print axioms Sun28.RealRatio.embedding_cases
#print axioms Sun28.RealRatio.zAt_ne
#print axioms Sun28.RealRatio.choose_real_indices
#print axioms Sun28.RealRatio.paper_translates_finite
#print axioms Sun28.RealRatio.entries_on_shared_indices
