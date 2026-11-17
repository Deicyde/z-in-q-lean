import MarkedMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Cartesian derivatives of the conformal factor away from the marked points. -/
namespace ZInQBlueprint.FiveMetric
open Real Finset
noncomputable section

def radial (x y : ℝ) := √(x^2+y^2)

private theorem radial_deriv (x y : ℝ) (hr:0<radial x y) :
    HasDerivAt (fun t=>radial t y) (x/radial x y) x := by
  have q : 0<x^2+y^2 := lt_of_not_ge (fun hn=>by
    rw [radial,Real.sqrt_eq_zero_of_nonpos hn] at hr
    exact lt_irrefl _ hr)
  have h := (((hasDerivAt_id x).pow 2).add_const (y^2)).sqrt q.ne'
  change HasDerivAt (fun t=>radial t y) ((2:ℝ)*x^(2-1)*1/(2*radial x y)) x at h
  convert h using 1
  ring

private theorem radial_second (x y : ℝ) (hr:0<radial x y) :
    HasDerivAt (fun t=>t/radial t y) (y^2/radial x y^3) x := by
  have q := Real.sq_sqrt (show 0≤x^2+y^2 by positivity)
  change radial x y ^ 2= _ at q
  have h := (hasDerivAt_id x).div (radial_deriv x y hr) hr.ne'
  change HasDerivAt (fun t=>t/radial t y) ((1*radial x y-x*(x/radial x y))/radial x y^2) x at h
  convert h using 1
  field_simp [hr.ne']
  nlinarith only [q]

private theorem coordinates (z : ℂ) (i : Fin 4) :
    radius z i=radial (z.re-(mark i).re) (z.im-(mark i).im) := by
  simp only [radius,Complex.norm_def,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,radial,pow_two]

def partialX (z : ℂ) (i : Fin 4) := (z.re-(mark i).re)/radius z i
def partialY (z : ℂ) (i : Fin 4) := (z.im-(mark i).im)/radius z i

theorem gradient_sq (z : ℂ) (off:∀ i,0<radius z i) :
    (∑ i,partialX z i)^2+(∑ i,partialY z i)^2 ≤ 16 := by
  have unit (i : Fin 4) : partialX z i^2+partialY z i^2=1 := by
    have q:=Real.sq_sqrt (show 0≤(z.re-(mark i).re)^2+(z.im-(mark i).im)^2 by positivity)
    change radial _ _ ^2=_ at q
    rw [←coordinates z i] at q
    unfold partialX partialY
    rw [div_pow,div_pow,←add_div,←q,div_self (pow_ne_zero 2 (off i).ne')]
  have cs (v : Fin 4→ℝ) : (∑ i,v i)^2≤4*∑ i,v i^2 := by
    simpa using sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin 4=>(1:ℝ)) v
  have add : (∑ i,partialX z i^2)+(∑ i,partialY z i^2)=4 := by
    rw [←sum_add_distrib]; simp only [unit,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one]
  linarith only [cs (partialX z),cs (partialY z),add]

private theorem line_second (x y : ℝ) (hr:0<radial x y) :
    deriv (fun t=>deriv (fun u=>radial u y) t) x = y^2/radial x y^3 := by
  have cont : Continuous fun t=>radial t y:=by unfold radial; fun_prop
  have near : (fun t=>deriv (fun u=>radial u y) t) =ᶠ[nhds x] fun t=>t/radial t y := by
    filter_upwards [(cont.isOpen_preimage _ isOpen_Ioi).mem_nhds hr] with t ht using (radial_deriv t y ht).deriv
  exact (near.deriv_eq).trans (radial_second x y hr).deriv

/-- The actual Cartesian Laplacian of each distance to a mark, in coordinates centered there. -/
theorem laplacian_distance (z : ℂ) (i : Fin 4) (off : 0<radius z i) :
    let x:=z.re-(mark i).re
    let y:=z.im-(mark i).im
    deriv (fun t=>deriv (fun u=>radial u y) t) x+
      deriv (fun t=>deriv (fun u=>radial x u) t) y=1/radius z i := by
  rw [coordinates] at off ⊢
  dsimp only
  set x:=z.re-(mark i).re
  set y:=z.im-(mark i).im
  have commute (t:ℝ) : radial x t=radial t x := by simp only [radial,add_comm]
  have eq : radial y x=radial x y := (commute y).symm
  simp_rw [commute]
  rw [line_second x y off,line_second y x (eq.symm ▸ off),eq]
  have q:=Real.sq_sqrt (show 0≤x^2+y^2 by positivity)
  change radial x y^2=_ at q
  field_simp [off.ne']
  nlinarith only [q]

end
end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.gradient_sq
#print axioms ZInQBlueprint.FiveMetric.laplacian_distance
