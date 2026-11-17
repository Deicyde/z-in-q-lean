import OriginalConcentrated

namespace ZInQBlueprint.OriginalConcentrated
open scoped Classical
open Finset Sun28.Ordinary ZInQ.RouteK ZInQBlueprint.OriginalHeightCount
noncomputable section
set_option maxRecDepth 12000

/-- Cubic obtained from the four retained projective factors, in a chart with a root at infinity. -/
def cubic (j:Fin 5) (t:ℚ) : ℚ :=
  ![(1-t)*(1-2401*t)*(32+343*t),(t-1)*(t-2401)*(32*t+343),
    t*(t-2401)*(32*t+343),t*(t-1)*(32*t+343),t*(t-1)*(t-2401)] j

def chart (j:Fin 5) (x:ℚ) := if j=0 then x⁻¹ else x

private theorem chart_product (j:Fin 5) (A B:ℤ) (nA:A≠0) (nB:B≠0) :
    ((fourProduct j A B:ℤ):ℚ) = (if j=0 then (A:ℚ) else (B:ℚ))^4*
      cubic j (if j=0 then (B:ℚ)/(A:ℚ) else (A:ℚ)/(B:ℚ)) := by
  have a : (A:ℚ)≠0:=by exact_mod_cast nA
  have b : (B:ℚ)≠0:=by exact_mod_cast nB
  fin_cases j <;> norm_num [fourProduct,Fin.prod_univ_four,keep,Fin.succAbove,oldForm,cubic] <;>
    field_simp

def baseCoordinate (j:Fin 5) (x:ℚ) : ℚ := if j=0 then (x.num:ℚ) else x.den

theorem homogeneous_chart {x:ℚ} (off:offMarks x) (j:Fin 5) :
    ((fourProduct j x.num x.den:ℤ):ℚ)=(baseCoordinate j x)^4*cubic j (chart j x) := by
  have a : x.num≠0:=by simpa [oldForm] using off 1
  have b : (x.den:ℤ)≠0:=by exact_mod_cast x.den_ne_zero
  have ex:=chart_product j x.num x.den a b
  push_cast at ex
  have inv : ((x.den:ℚ)/(x.num:ℚ))=x⁻¹:=by simpa only [inv_div] using congrArg Inv.inv x.num_div_den
  simpa only [baseCoordinate,chart,inv,x.num_div_den] using ex

/-- A nonbranch rational point on a smooth-supported twist of the retained cubic. -/
def OnTwist (j:Fin 5) (x:ℚ) (d:ℤ) : Prop := ∃ y:ℚ,y≠0 ∧ y^2=(d:ℚ)*cubic j (chart j x)

private theorem base_ne {x:ℚ} (off:offMarks x) (j:Fin 5) : baseCoordinate j x≠0 := by
  have a : x.num≠0:=by simpa [oldForm] using off 1
  unfold baseCoordinate
  split
  · exact_mod_cast a
  · exact_mod_cast x.den_ne_zero

theorem point_on_twist {x:ℚ} (off:offMarks x) (j:Fin 5) : OnTwist j x (signedTwist j x) := by
  have pn : fourProduct j x.num x.den ≠0 := Finset.prod_ne_zero_iff.mpr (fun l _=>off (keep j l))
  obtain ⟨sf,w,wn,eq⟩:=sqfInt_spec pn
  change fourProduct j x.num x.den=signedTwist j x*w^2 at eq
  have ep:=homogeneous_chart off j
  rw [eq] at ep
  push_cast at ep
  have dn : (signedTwist j x:ℚ)≠0 := by exact_mod_cast sf.ne_zero
  have v : (w:ℚ)≠0:=by exact_mod_cast wn
  have bn:=base_ne off j
  refine ⟨(signedTwist j x:ℚ)*w/(baseCoordinate j x)^2,by positivity,?_⟩
  field_simp
  exact ep

theorem twist_dvd {x:ℚ} (off:offMarks x) {j:Fin 5} {d:ℤ} (point:OnTwist j x d) :
    signedTwist j x ∣ d := by
  obtain ⟨y,yn,py⟩:=point
  have pn : fourProduct j x.num x.den ≠0 := Finset.prod_ne_zero_iff.mpr (fun l _=>off (keep j l))
  obtain ⟨sf,w,wn,eq⟩:=sqfInt_spec pn
  change fourProduct j x.num x.den=signedTwist j x*w^2 at eq
  apply sf.dvd_of_isSquare_mul
  apply Rat.isSquare_intCast_iff.mp
  change IsSquare (((signedTwist j x)*d:ℤ):ℚ)
  push_cast
  have ep:=homogeneous_chart off j
  rw [eq] at ep
  push_cast at ep
  have v : (w:ℚ)≠0:=by exact_mod_cast wn
  refine ⟨(baseCoordinate j x)^2*y/w,?_⟩
  field_simp
  linear_combination (d:ℚ)*ep-(baseCoordinate j x)^4*py

theorem concentrated_iff_cubic {x:ℚ} (off:offMarks x) (j:Fin 5) :
    Concentrated x j ↔ ∃ d:ℤ,d.natAbs ∣ 210 ∧ OnTwist j x d := by
  constructor
  · intro h; exact ⟨_,(concentrated_iff_twist off j).mp h,point_on_twist off j⟩
  · rintro ⟨d,small,point⟩; exact (concentrated_iff_twist off j).mpr ((Int.natAbs_dvd_natAbs.mpr (twist_dvd off point)).trans small)

end
end ZInQBlueprint.OriginalConcentrated
#print axioms ZInQBlueprint.OriginalConcentrated.homogeneous_chart
#print axioms ZInQBlueprint.OriginalConcentrated.point_on_twist
#print axioms ZInQBlueprint.OriginalConcentrated.twist_dvd
#print axioms ZInQBlueprint.OriginalConcentrated.concentrated_iff_cubic

