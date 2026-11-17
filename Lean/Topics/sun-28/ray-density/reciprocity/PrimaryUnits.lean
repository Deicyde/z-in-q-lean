import GaussianCRT
import PrimaryGroup

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

namespace Sun28.Reciprocity
open Sun28.RayDensity Sun28.RayDensity.Artin
noncomputable section

def imaginary : GaussianIntˣ :=
  ⟨⟨0,1⟩,⟨0,-1⟩,by decide,by decide⟩

def quarter (j:Fin 4) : GaussianIntˣ := imaginary^j.val

theorem global_units (u:GaussianIntˣ) : ∃ j:Fin 4, u=quarter j := by
  let q:GaussianInt:=u
  have one : q.norm=1 := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ)≤0) q).2 u.isUnit
  rw [Zsqrtd.norm_def] at one
  have l : -1≤q.re := by nlinarith only [one,sq_nonneg q.im,sq_nonneg (q.re+1)]
  have h : q.re≤1 := by nlinarith only [one,sq_nonneg q.im,sq_nonneg (q.re-1)]
  have ll : -1≤q.im := by nlinarith only [one,sq_nonneg q.re,sq_nonneg (q.im+1)]
  have hh : q.im≤1 := by nlinarith only [one,sq_nonneg q.re,sq_nonneg (q.im-1)]
  interval_cases hr:q.re <;> interval_cases hi:q.im <;> simp_all
  all_goals first
    | exact ⟨0,Units.ext (Zsqrtd.ext (by exact hr) (by exact hi))⟩
    | exact ⟨1,Units.ext (Zsqrtd.ext (by exact hr) (by exact hi))⟩
    | exact ⟨2,Units.ext (Zsqrtd.ext (by exact hr) (by exact hi))⟩
    | exact ⟨3,Units.ext (Zsqrtd.ext (by exact hr) (by exact hi))⟩

def primaryRing : Primary →* GR 16 where
  toFun a:=⟨a.val.1,a.val.2⟩
  map_one':=rfl
  map_mul' x y:=by
    apply QuadraticAlgebra.ext
    · change x.val.1*y.val.1-x.val.2*y.val.2=_
      simp;ring
    · change x.val.1*y.val.2+x.val.2*y.val.1=_
      simp

def primaryUnit : Primary →* GU 16 :=
  (Units.map primaryRing).comp toUnits.toMonoidHom

@[simp] theorem primaryUnit_coords (x:Primary) : coords (primaryUnit x)=x.val := rfl

def reducedUnit (m:ℕ) : GaussianIntˣ →* GU m := Units.map (gaussianRed m).toMonoidHom

theorem quarter_action (v:GU 16) (j:Fin 4) :
    coords (v*reducedUnit 16 (quarter j))=turn j (coords v) := by
  fin_cases j <;> apply Prod.ext <;>
    simp [coords,reducedUnit,gaussianRed,quarter,imaginary,turn,QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul,pow_succ]

theorem dyadic_odd (v:GU 16) : (pairNorm (coords v)).val%2=1 := by
  have e: pairNorm (coords v) * (unitNorm 16 (v⁻¹):ZMod 16) = 1 := by
    change ((v:GR 16).re^2+(v:GR 16).im^2) * _ = _
    rw [← norm_coordinates]
    exact congrArg Units.val (show unitNorm 16 v * unitNorm 16 (v⁻¹) = 1 by
      rw [←map_mul,mul_inv_cancel,map_one])
  exact (by decide : ∀ a b:ZMod 16,a*b=1 → a.val%2=1) _ _ e

theorem normalized_unit (v:GU 16) :
    ∃ j:Fin 4, coords (v*reducedUnit 16 (quarter j))∈primarySet := by
  obtain ⟨j,h⟩ := (show ∀ z:Pair 16,(pairNorm z).val%2=1 → ∃ j:Fin 4,turn j z∈primarySet by decide)
    (coords v) (dyadic_odd v)
  exact ⟨j,quarter_action v j ▸ h⟩

theorem unit_trivial_on_primary (v:GU 16) (u:GaussianIntˣ)
    (hv:coords v∈primarySet) (hu:coords (v*reducedUnit 16 u)∈primarySet) : u=1 := by
  obtain ⟨j,rfl⟩:=global_units u
  rw [quarter_action] at hu
  have e:= (show ∀ z∈primarySet, ∀ j:Fin 4, turn j z∈primarySet → j=0 by decide)
    _ hv j hu
  simp [e,quarter]

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.global_units
#print axioms Sun28.Reciprocity.quarter_action
#print axioms Sun28.Reciprocity.normalized_unit
#print axioms Sun28.Reciprocity.unit_trivial_on_primary
