import HilbertArtin

/-! The finite local conductor needs only an action of inertia. The values of
the codimensions below are genuine invariant dimensions for that action. -/

open NumberField Finset
open scoped NumberField Pointwise
open ZInQKernel.Contrib.HilbertDifferent
open Sun28.SurfaceHeight.HilbertArtin

namespace Sun28.SurfaceHeight.InertiaArtin

variable (L : Type) [Field L] [NumberField L]
variable (P : Ideal (𝓞 L))
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

abbrev inertia := P.inertia (L ≃ₐ[ℚ] L)

noncomputable def lowerCodim (σ : Representation k (inertia L P) V) (j : ℕ) : ℕ :=
  Module.finrank k V - Module.finrank k
    (Representation.invariants (σ.comp (Subgroup.inclusion
      (P.ramificationGroup_le_inertia (G := L ≃ₐ[ℚ] L) j))))

theorem lowerCodim_zero (σ : Representation k (inertia L P) V) (j : ℕ)
    (trivial : ramGroup L P j = ⊥) : lowerCodim L P σ j = 0 := by
  have top : Representation.invariants (σ.comp (Subgroup.inclusion
      (P.ramificationGroup_le_inertia (G := L ≃ₐ[ℚ] L) j))) = ⊤ := by
    apply top_unique
    intro v _ g
    have hg : g.1 ∈ ramGroup L P j := g.2
    rw [trivial, Subgroup.mem_bot] at hg
    have hone : g = 1 := Subtype.ext hg
    simp [hone]
  have hdim := congrArg (fun W : Submodule k V => Module.finrank k W) top
  have ht : Module.finrank k (⊤ : Submodule k V) = Module.finrank k V := by simp
  exact Nat.sub_eq_zero_of_le (hdim.trans ht).ge

theorem lowerCodim_restrict (ρ : Representation k (decompositionGroup L P) V) (j : ℕ) :
    lowerCodim L P (ρ.comp (Subgroup.inclusion
      (Ideal.inertia_le_stabilizer (M := L ≃ₐ[ℚ] L) P))) j = fixedCodim L P ρ j := rfl

noncomputable def partialSum (σ : Representation k (inertia L P) V) (n : ℕ) : ℚ :=
  (lowerCodim L P σ 0 : ℚ) + (∑ j ∈ range n,
    ramCard L P (j+1) * lowerCodim L P σ (j+1) : ℕ) / (P.ramificationIdx ℤ : ℚ)

variable [IsGalois ℚ L] (p : ℕ) [Fact p.Prime] [P.IsPrime]
variable [P.LiesOver (Ideal.span {(p : ℤ)})]

theorem partial_le (σ : Representation k (inertia L P) V) (n : ℕ) :
    partialSum L P σ n ≤ (Module.finrank k V : ℚ) *
      (1 + 2 * (padicValNat p (P.ramificationIdx ℤ) : ℚ)) := by
  let d := Module.finrank k V
  let e := P.ramificationIdx ℤ
  have he : 0 < e := Ideal.ramificationIdx_pos ℤ P
  have hc (j : ℕ) : lowerCodim L P σ j ≤ d := Nat.sub_le _ _
  have w := weighted_wild_le L p P d n (fun j => lowerCodim L P σ (j+1))
    (fun j => lowerCodim_zero L P σ (j+1)) (fun j => hc (j+1))
  have hr : (0:ℚ) < e := by exact_mod_cast he
  have hq : (∑ j ∈ range n, ramCard L P (j+1) * lowerCodim L P σ (j+1) : ℕ) /
      (e : ℚ) ≤ 2*(d : ℚ)*padicValNat p e := by
    apply (div_le_iff₀ hr).2
    norm_cast
    simpa [mul_assoc, mul_comm, mul_left_comm, e] using w
  have ht : (lowerCodim L P σ 0 : ℚ) ≤ d := by exact_mod_cast hc 0
  change (lowerCodim L P σ 0 : ℚ) + _ ≤ (d : ℚ) * (1+2*(padicValNat p e : ℚ))
  linarith

noncomputable def conductor (σ : Representation k (inertia L P) V) : ℚ :=
  partialSum L P σ (Classical.choose (exists_termination L p P))

theorem conductor_le [FiniteDimensional k V] (σ : Representation k (inertia L P) V) :
    conductor L P p σ ≤ (Module.finrank k V : ℚ) *
      (1 + 2 * (padicValNat p (P.ramificationIdx ℤ) : ℚ)) :=
  partial_le L P p σ _

theorem conductor_restrict (ρ : Representation k (decompositionGroup L P) V) :
    conductor L P p (ρ.comp (Subgroup.inclusion
      (Ideal.inertia_le_stabilizer (M := L ≃ₐ[ℚ] L) P))) = artinConductor L p P ρ := rfl

end Sun28.SurfaceHeight.InertiaArtin

#print axioms Sun28.SurfaceHeight.InertiaArtin.lowerCodim_zero
#print axioms Sun28.SurfaceHeight.InertiaArtin.lowerCodim_restrict
#print axioms Sun28.SurfaceHeight.InertiaArtin.partial_le
#print axioms Sun28.SurfaceHeight.InertiaArtin.conductor_le
#print axioms Sun28.SurfaceHeight.InertiaArtin.conductor_restrict
