import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

namespace ZInQBlueprint.MarkedFibre

variable {G D T L : Type*} [Group G] [MulAction G D] [MulAction G T] [MulAction G L]

/-- Galois equivariance of a faithful Tate representation on endomorphisms
gives a fixed endomorphism ring whenever inertia fixes the Tate module. -/
theorem fixes_endomorphisms {R : Type*} [CommRing R] [Ring D] [AddCommGroup T] [Module R T]
    (ρ : D →+* Module.End R T) (faithful : Function.Injective ρ)
    (equivariant : ∀ (g : G) (d : D) (v : T), ρ (g • d) (g • v) = g • (ρ d v))
    {g : G} (trivialTate : ∀ v : T, g • v = v) (d : D) : g • d = d := by
  apply faithful
  ext v
  simpa only [trivialTate] using equivariant g d v

/-- A surjective equivariant reduction from a Tate module transmits trivial inertia to
the full level group. -/
theorem fixes_level (red : T → L) (onto : Function.Surjective red)
    (equivariant : ∀ (g : G) (t : T), red (g • t) = g • red t)
    {g : G} (h : ∀ t : T, g • t = t) (z : L) : g • z = z := by
  obtain ⟨t,rfl⟩ := onto z
  rw [← equivariant, h]

/-- Markings on a fixed polarized surface consist of an endomorphism tuple and
a level tuple satisfying a predicate. An equivariant surjection covers the geometric
fibre, allowing automorphisms and repeated presentations. -/
theorem fixes_marked_fibre {O B X : Type*} [MulAction G X]
    {marks : (O → D) → (B → L) → Prop}
    (π : ∀ (ι : O → D) (η : B → L), marks ι η → X)
    (onto : ∀ x, ∃ ι η h, π ι η h = x)
    (preserve : ∀ (g : G) ι η, marks ι η → marks (fun o => g • ι o) (fun b => g • η b))
    (equivariant : ∀ (g : G) ι η h,
      g • π ι η h = π (fun o => g • ι o) (fun b => g • η b) (preserve g ι η h))
    {g : G} (hD : ∀ d : D, g • d = d) (hL : ∀ l : L, g • l = l) (x : X) : g • x = x := by
  obtain ⟨ι, η, h, rfl⟩ := onto x
  simp only [equivariant, hD, hL]

end ZInQBlueprint.MarkedFibre

#print axioms ZInQBlueprint.MarkedFibre.fixes_endomorphisms
#print axioms ZInQBlueprint.MarkedFibre.fixes_level
#print axioms ZInQBlueprint.MarkedFibre.fixes_marked_fibre
