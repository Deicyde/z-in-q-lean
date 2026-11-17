import OrdinaryGeometry
import PrimitiveParameters
import GlobalTwist
import DDMMCompletion

/-! A proper smooth model of the original rational paper curve at every ordinary prime. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial IsDiscreteValuationRing
open ZInQBlueprint.BinaryCover ZInQBlueprint.PrimitiveParameters ZInQBlueprint.IntegralSextic
open ZInQBlueprint.RationalClusters ZInQBlueprint.GlobalTwist
namespace ZInQBlueprint.OrdinaryModel
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "Zp" => ℤ_[p]
local notation "Qp" => ℚ_[p]

def scale (u : ℚ) (a : Zpˣ) : Zp := -6*(delta u:Zp)*(G p u)*1*(a:Zp)^2

private theorem parameters (u : ℚ) (hp : 7≤p) (hF : IsUnit (F p u)) (hG : IsUnit (G p u)) :
    ∃ t a : Zpˣ, Coordinates p u (t:Zp) 1 (a:Zp) ∧ IsUnit ((t:Zp)^2+27) ∧ IsUnit (scale p u a) := by
  have h30 := (unit_nat p 2 (by decide) (by omega)).mul ((unit_nat p 3 (by decide) (by omega)).mul
    (unit_nat p 5 (by decide) (by omega)))
  have hprod : IsUnit (left p u*right p u) := by
    rw [show left p u*right p u=30*F p u from (parameter_identities _ _).1]
    exact (by convert h30 using 1; norm_num : IsUnit (30:Zp)).mul hF
  let a := (isUnit_of_mul_isUnit_left hprod).unit
  let b := (isUnit_of_mul_isUnit_right hprod).unit
  let t := a⁻¹*b
  have ha : (a:Zp)=left p u := IsUnit.unit_spec _
  have hb : (b:Zp)=right p u := IsUnit.unit_spec _
  have ht : (a:Zp)*(t:Zp)=right p u := by simp [t,hb]
  have he : (a:Zp)^2*((t:Zp)^2+27)=(G p u)^3 := by
    have h : (G p u)^3=27*(left p u)^2+(right p u)^2 := (parameter_identities _ _).2.1
    rw [←ht,←ha] at h
    linear_combination -h
  have ds : IsUnit (delta u:Zp) := addVal_eq_zero_iff.mp ((ordinary p u (addVal_eq_zero_iff.mpr hF)).padic_val)
  have six : IsUnit (6:Zp) := unit_nat p 6 (by decide) (by omega)
  exact ⟨t,a,.first rfl ha ht,isUnit_of_mul_isUnit_right (he ▸ hG.pow 3),
    (((six.neg.mul ds).mul hG).mul isUnit_one).mul (a.isUnit.pow 2)⟩

private theorem open_pullback {S T : Scheme} (f : T ⟶ S) {A C : Over S}
    (j : A ⟶ C) [IsOpenImmersion j.left] : IsOpenImmersion ((Over.pullback f).map j).left := by
  let m : pullback A.hom f ⟶ pullback C.hom f := ((Over.pullback f).map j).left
  have H : m ≫ pullback.snd C.hom f = pullback.snd A.hom f := ((Over.pullback f).map j).w
  have sq : IsPullback (pullback.fst A.hom f) m j.left (pullback.fst C.hom f) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd C.hom f) (v₂₂ := C.hom) (h₃₁ := f)
    · rw [H,j.w]
      exact IsPullback.of_hasPullback _ _
    · exact (pullback.lift_fst ..).symm
    · exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance

/-- The actual curve over Q_p extends, for p at least 7 prime to both forms, to a
smooth proper Z_p scheme with geometrically integral fibres. The chosen model
has the prescribed exterior quadratic twist. -/
theorem ordinary_curve_model {u : ℚ} (hu : u ∉ ZInQ.contactSet) (hp : 7≤p)
    (hF : IsUnit (F p u)) (hG : IsUnit (G p u)) :
    ∃ t a : Zpˣ, Coordinates p u (t:Zp) 1 (a:Zp) ∧
      let M := model (scale p u a) (t:Zp)
      Smooth M.hom ∧ IsProper M.hom ∧ GeometricallyIntegral M.hom ∧
      Nonempty (paperPullback Qp u ≅ (Over.pullback (scalarMap Zp Qp)).obj M) := by
  obtain ⟨t,a,hc,hD,hs⟩ := parameters p u hp hF hG
  have h2 : IsUnit (2:Zp) := unit_nat p 2 (by decide) (by omega)
  let s := scale p u a
  let P := chartPair s (t:Zp)
  let M := model s (t:Zp)
  let D := (Over.pullback (scalarMap Zp Qp)).obj M
  have sm := smooth_proper hs h2 t.isUnit hD
  refine ⟨t,a,hc,sm.1,sm.2,geom_integral hs h2 t.isUnit hD,?_⟩
  let : IsProper M.hom := sm.2
  let : IsProper D.hom := inferInstanceAs (IsProper (pullback.snd M.hom (scalarMap Zp Qp)))
  have reg := field_chart hs h2 t.isUnit hD Qp (algebraMap Zp Qp)
  let : AlgebraicGeometry.IsIntegral D.left := IntegralCover.fibre_integral Zp P
    (overlap s (t:Zp)) Qp (fun i => (reg i).1)
  let j := IntegralCover.chartMap Zp P (overlap s (t:Zp)) false
  let : IsOpenImmersion j.left := chartInclusion_open Zp (P false) (P true) (overlap s (t:Zp)) false
  let e := affineBaseChange Zp Qp (P false)
  let k := e.hom ≫ (Over.pullback (scalarMap Zp Qp)).map j
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  have hk : IsOpenImmersion k.left := @IsOpenImmersion.comp _ _ _ e.hom.left _ (IsOpenImmersion.of_isIso _)
    (open_pullback _ j)
  have vh : ∀ x : D.left, PreValuationRing (D.left.presheaf.stalk x) :=
    IntegralCover.fibre_prevaluation Zp P (overlap s (t:Zp)) Qp (fun i => (reg i).2)
  obtain ⟨j₀,_,uniq⟩ := unique_ddmm_completion hu (1 : Zpˣ) a (t:Zp) hc
  obtain ⟨iso,_,_⟩ := @uniq D (inferInstanceAs (IsProper D.hom)) (inferInstanceAs (AlgebraicGeometry.IsIntegral D.left)) k hk vh
  exact ⟨iso⟩

end
end ZInQBlueprint.OrdinaryModel
#print axioms ZInQBlueprint.OrdinaryModel.ordinary_curve_model
