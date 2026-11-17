import CechQuotient
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.LeftExact

/-! Sheaf cohomology and its actual base-field action on the small Zariski site. -/
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ZInQBlueprint.BinaryCover.Cech
noncomputable section
set_option synthInstance.maxHeartbeats 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : Scheme.{0})

/-- The additive structure sheaf on the opens of X. -/
def additiveStructure : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} :=
  (sheafCompose _ (forget₂ RingCat AddCommGrpCat)).obj
    ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf)

/-- Mathlib's Ext-defined first cohomology of the structure sheaf. -/
abbrev H1 : Type := Sheaf.H.{0} (additiveStructure X) 1

variable {X} {k : Type} [Field k] (p : X ⟶ Spec (.of k))

/-- The section of the structure sheaf on an open pulled back from a base scalar. -/
def scalarSection (U : X.Opens) : k →+* Γ(X,U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U le_top).hom

private theorem restrict_scalar {U V : X.Opensᵒᵖ} (i : U ⟶ V) (r : k) :
    X.presheaf.map i (scalarSection p U.unop r) = scalarSection p V.unop r := by
  let c := (Scheme.ΓSpecIso (CommRingCat.of k)).inv r
  change X.presheaf.map i (p.appLE ⊤ U.unop le_top c) = p.appLE ⊤ V.unop le_top c
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (p.appLE_map le_top i)) c

/-- Multiplication by the pullback of a scalar on the additive structure sheaf. -/
def scalarEnd (r : k) : additiveStructure X ⟶ additiveStructure X := ⟨{
  app U := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (scalarSection p U.unop r))
  naturality := by
    intro U V i
    ext x
    change Γ(X,U.unop) at x
    change scalarSection p V.unop r * (X.presheaf.map i x) = X.presheaf.map i (scalarSection p U.unop r * x)
    rw [map_mul,restrict_scalar] }⟩

private theorem scalar_one : scalarEnd p 1 = 𝟙 _ := by
  ext U x
  change Γ(X,U.unop) at x
  change scalarSection p U.unop 1 * x = x
  simp

private theorem scalar_add (r s : k) : scalarEnd p (r+s) = scalarEnd p r + scalarEnd p s := by
  ext U x
  change Γ(X,U.unop) at x
  change scalarSection p U.unop (r+s)*x = scalarSection p U.unop r*x + scalarSection p U.unop s*x
  rw [map_add,add_mul]

private theorem scalar_mul (r s : k) : scalarEnd p (r*s) = scalarEnd p s ≫ scalarEnd p r := by
  ext U x
  change Γ(X,U.unop) at x
  change scalarSection p U.unop (r*s)*x = scalarSection p U.unop r*(scalarSection p U.unop s*x)
  rw [map_mul,mul_assoc]

/-- Cohomological scalars act by functoriality in the coefficient sheaf. -/
@[instance_reducible] def h1Module : Module k (H1 X) := by
  let : SMul k (H1 X) := ⟨fun r x => Sheaf.H.map (scalarEnd p r) 1 x⟩
  apply Module.ofMinimalAxioms
  · exact fun r => (Sheaf.H.map (scalarEnd p r) 1).map_add
  · intro r s x
    change Sheaf.H.map (scalarEnd p (r+s)) 1 x = _
    rw [scalar_add, Sheaf.H.map_add_apply]
    rfl
  · intro r s x
    change Sheaf.H.map (scalarEnd p (r*s)) 1 x = _
    rw [scalar_mul, Sheaf.H.map_comp_apply]
    rfl
  · intro x
    change Sheaf.H.map (scalarEnd p 1) 1 x = _
    rw [scalar_one,Sheaf.H.map_id_apply]

theorem h1_smul (r : k) (x : H1 X) :
    letI := h1Module p
    r • x = Sheaf.H.map (scalarEnd p r) 1 x := rfl

/-- Open comparison assertion for the particular atlas. It says its restriction
cokernel computes actual H¹ of the structure sheaf as a vector space over k. -/
def SheafComparison [CharZero k] (u : ℚ) : Prop :=
  letI := h1Module (paperModel k u).hom
  Nonempty ((Punctured k (paper k u false) ⧸
    LinearMap.range (differential k (paper_overlap k u))) ≃ₗ[k] H1 (paperModel k u).left)

/-- Consequence of the pending comparison, with the geometric coefficient action fixed. -/
theorem paper_h1_finrank [CharZero k] (u : ℚ) (h : SheafComparison (k := k) u) :
    letI := h1Module (paperModel k u).hom
    Module.finrank k (H1 (paperModel k u).left) = 2 := by
  let := h1Module (paperModel k u).hom
  obtain ⟨e⟩ := h
  exact e.finrank_eq.symm.trans (paper_quotient_finrank k u)

end
end ZInQBlueprint.BinaryCover.Cech
#print axioms ZInQBlueprint.BinaryCover.Cech.h1Module
#print axioms ZInQBlueprint.BinaryCover.Cech.h1_smul
#print axioms ZInQBlueprint.BinaryCover.Cech.SheafComparison
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_h1_finrank
