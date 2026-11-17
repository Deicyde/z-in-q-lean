import SignedCanonicalTheta
import ThetaSupportTransport
import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.InvertibleEqPullbackSectionEq

/-! Pullback of global sections detects all sections on a reduced target when
the morphism covers its points over an algebraically closed ground field. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace ZInQBlueprint.DeterminantSections
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Over (Spec (.of k))}
set_option maxHeartbeats 320000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def sectionOfGlobal {V : Scheme.{u}} (M : V.Modules) (x : Γ(M,⊤)) :
    (M : SheafOfModules V.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk (fun _ => M.presheaf.map (homOfLE le_top).op x) (by
    intro U W i
    change (M.presheaf.map (homOfLE le_top).op ≫ M.presheaf.map i) x = _
    rw [← M.presheaf.map_comp]
    rfl)

private def asHom {V : Scheme.{u}} (M : V.Modules) (x : Γ(M,⊤)) : 𝟙_ V.Modules ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M x)

private def atOne {V : Scheme.{u}} {M : V.Modules} (s : 𝟙_ V.Modules ⟶ M) : Γ(M,⊤) :=
  s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)

private theorem atOne_asHom {V : Scheme.{u}} (M : V.Modules) (x : Γ(M,⊤)) :
    atOne (asHom M x) = x := by
  change (1 : Γ(V,⊤)) • M.presheaf.map (𝟙 _) x = x
  rw [one_smul,M.presheaf.map_id]
  rfl

private theorem zero_of_atOne {V : Scheme.{u}} {M : V.Modules} (s : 𝟙_ V.Modules ⟶ M)
    (h : atOne s = 0) : s = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  have hm : m = Scheme.Modules.ofUnitSection U m • Scheme.Modules.toUnitSection U (1 : Γ(V,U)) := by
    apply Scheme.Modules.ofUnitSection_injective U
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
  have h1 : Scheme.Modules.toUnitSection U (1 : Γ(V,U)) =
      (𝟙_ V.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (Scheme.Modules.toUnitSection ⊤ 1) := by
    apply Scheme.Modules.ofUnitSection_injective U
    rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
      Scheme.Modules.ofUnitSection_toUnitSection, map_one]
  have hn := s.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op
  have e := ConcreteCategory.congr_hom hn (Scheme.Modules.toUnitSection ⊤ 1)
  change s.app U ((𝟙_ V.Modules).presheaf.map _ _) = M.presheaf.map _ (atOne s) at e
  rw [hm, Scheme.Modules.Hom.app_smul, h1, e, h, map_zero, smul_zero, Scheme.Modules.Hom.zero_app]
  rfl

private theorem pull_zero {V W : Scheme.{u}} (f : W ⟶ V) (L : V.Modules) :
    Scheme.Modules.pullbackSection f (0 : 𝟙_ _ ⟶ L) = 0 := by
  change (Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map 0 = 0
  rw [Functor.map_zero,comp_zero]

theorem hom_pull_injective (f : Y ⟶ X) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    {L : X.left.Modules} (hL : L.IsInvertible)
    (surj : Function.Surjective (fun p : Over.mk (𝟙 _) ⟶ Y => p ≫ f)) :
    Function.Injective (Scheme.Modules.pullbackSection (M:=L) f.left) := by
  intro s t h
  have sub : Scheme.Modules.pullbackSection f.left (s-t) = 0 := by
    change (Scheme.Modules.pullbackUnitIso _).inv ≫ (Scheme.Modules.pullback _).map (s-t) = 0
    rw [Functor.map_sub,Preadditive.comp_sub]
    exact sub_eq_zero.mpr h
  apply sub_eq_zero.mp
  apply hL.eq_of_forall_pullbackSection_eq X.hom
  intro p hp
  let w : Over.mk (𝟙 _) ⟶ X := Over.homMk p hp
  obtain ⟨q,hq⟩ := surj w
  have ew : q.left ≫ f.left = p := congrArg (·.left) hq
  rw [pull_zero,←ew]
  have vv : Scheme.Modules.pullbackSection q.left (Scheme.Modules.pullbackSection f.left (s-t)) = 0 := by
    rw [sub,pull_zero]
  rw [(hL.pullback f.left).pullbackSection_eq_zero_iff_mem_support, ←hL.comap_zeroSchemeIdeal,
    Scheme.IdealSheafData.support_comap] at vv
  exact (hL.pullbackSection_eq_zero_iff_mem_support (s-t) (q.left ≫ f.left)).mpr vv

private def ringAction {V : Scheme.{u}} (M : V.Modules) (r : Γ(V,⊤)) (x : Γ(M,⊤)) : Γ(M,⊤) := r • x

/-- Global sections with the scalar action given by the structural morphism. -/
def sectionsPull (f : Y ⟶ X) (L : X.left.Modules) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom X.hom L ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Y.hom ((Scheme.Modules.pullback f.left).obj L) ⊤
    Γ(L,⊤) →ₗ[k] Γ((Scheme.Modules.pullback f.left).obj L,⊤) := by
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app L
  letI := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
  letI := Scheme.TwoAffineOpenCover.algebraOfHom Y.hom ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom X.hom L ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Y.hom ((Scheme.Modules.pullback f.left).obj L) ⊤
  refine { toFun := fun x => η.app ⊤ x, map_add' := fun _ _ => map_add _ _ _, map_smul' := ?_ }
  intro r x
  let M := (Scheme.Modules.pullback f.left).obj L
  change η.app ⊤ ((algebraMap k Γ(X.left,⊤) r) • x) = ringAction M (algebraMap k Γ(Y.left,⊤) r) (η.app ⊤ x)
  rw [Scheme.Modules.Hom.app_smul]
  change ringAction M (f.left.app ⊤ (algebraMap k Γ(X.left,⊤) r)) (η.app ⊤ x) =
    ringAction M (algebraMap k Γ(Y.left,⊤) r) (η.app ⊤ x)
  apply congrArg (fun a => ringAction M a (η.app ⊤ x))
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,←f.w]
  rw [Scheme.Hom.app_eq_appLE]
  change (X.hom.appLE ⊤ ⊤ le_top ≫ f.left.appLE ⊤ ⊤ le_rfl) _ = _
  erw [Scheme.Hom.appLE_comp_appLE]

theorem sectionsPull_injective (f : Y ⟶ X) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    {L : X.left.Modules} (hL : L.IsInvertible)
    (surj : Function.Surjective (fun p : Over.mk (𝟙 _) ⟶ Y => p ≫ f)) :
    Function.Injective (sectionsPull f L) := by
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom X.hom L ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Y.hom ((Scheme.Modules.pullback f.left).obj L) ⊤
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f.left
  let η := adj.unit.app L
  let s := asHom L x
  have eta : s ≫ η = 0 := by
    apply zero_of_atOne
    change η.app ⊤ (atOne (asHom L x)) = 0
    exact (congrArg (fun v : Γ(L,⊤) => η.app ⊤ v) (atOne_asHom L x)).trans hx
  have m : (Scheme.Modules.pullback f.left).map s = 0 := by
    apply (adj.homEquiv _ _).injective
    change adj.unit.app _ ≫ _ = adj.unit.app _ ≫ _
    rw [Functor.map_zero,comp_zero]
    exact (adj.unit.naturality s).symm.trans eta
  have s0 : s = 0 := by
    apply hom_pull_injective f hL surj
    rw [pull_zero]
    change (Scheme.Modules.pullbackUnitIso _).inv ≫ _ = 0
    rw [m,comp_zero]
  rw [←atOne_asHom L x]
  change atOne s = 0
  rw [s0]
  rfl

theorem rank_one_descends (f : Y ⟶ X) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    {L : X.left.Modules} (hL : L.IsInvertible) {s : 𝟙_ _ ⟶ L} (hs : s ≠ 0)
    (surj : Function.Surjective (fun p : Over.mk (𝟙 _) ⟶ Y => p ≫ f))
    (h : ThetaLinearSystem.rankH0 Y.hom ((Scheme.Modules.pullback f.left).obj L) = 1) :
    ThetaLinearSystem.rankH0 X.hom L = 1 := by
  let M := (Scheme.Modules.pullback f.left).obj L
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom X.hom L ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Y.hom M ⊤
  have one : Module.finrank k Γ(M,⊤) = 1 := h
  let : Module.Finite k Γ(M,⊤) := Module.finite_of_finrank_eq_succ one
  have inj := sectionsPull_injective f hL surj
  let : Module.Finite k Γ(L,⊤) := Module.Finite.of_injective _ inj
  let : Nontrivial Γ(L,⊤) := ⟨⟨atOne s,0,fun z => hs (zero_of_atOne s z)⟩⟩
  have lower : 0 < Module.finrank k Γ(L,⊤) := Module.finrank_pos
  have upper := LinearMap.finrank_le_finrank_of_injective inj
  change Module.finrank k Γ(L,⊤) = 1
  change Module.finrank k Γ(L,⊤) ≤ Module.finrank k Γ(M,⊤) at upper
  omega

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.hom_pull_injective
#print axioms ZInQBlueprint.DeterminantSections.sectionsPull_injective
#print axioms ZInQBlueprint.DeterminantSections.rank_one_descends
