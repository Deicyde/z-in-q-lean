import LogarithmicBudget

namespace Sun28.HeightCubics.Pooled.Logarithmic
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres
open private radical_large log_one from LogarithmicBudget
noncomputable section

/-- The multiplicative increase of the admissible even budget is strictly greater than one. -/
theorem log_cost_lt {t:ℝ} (large:62208≤t) : (Real.log t)^10<t^5 := by
  let w:=Real.sqrt t
  let y:=Real.sqrt w
  have tp:0<t:=by linarith
  have wp:0<w:=Real.sqrt_pos.mpr tp
  have yp:0<y:=Real.sqrt_pos.mpr wp
  have ww:w^2=t:=Real.sq_sqrt tp.le
  have yy:y^2=w:=Real.sq_sqrt wp.le
  have eq:y^4=t:=by calc
    y^4=(y^2)^2:=by ring
    _=t:=by rw [yy,ww]
  have yn:y≠1:=by intro e;rw [e,one_pow] at eq;linarith
  have logt:Real.log t=4*Real.log y:=by rw [←eq,Real.log_pow];norm_num
  have sharp:=Real.log_lt_sub_one_of_pos yp yn
  have law:Real.log t<w:=by linarith only [logt,sharp,yy,sq_nonneg (y-2)]
  have G:=pow_lt_pow_left₀ law ((log_one large).trans' (by norm_num : (0:ℝ)≤1)) (by decide : 10≠0)
  have er:w^10=t^5:=by calc
    w^10=(w^2)^5:=by ring
    _=t^5:=by rw [ww]
  rwa [er] at G

theorem budget_increase (A B:ℤ) : 1<(heightRadical A B:ℝ)^5 /
    (Real.log (heightRadical A B:ℝ))^10 := by
  have large:(62208:ℝ)≤(heightRadical A B:ℝ):=by exact_mod_cast radical_large A B
  have pos:0<Real.log (heightRadical A B:ℝ):=zero_lt_one.trans_le (log_one large)
  exact (one_lt_div (pow_pos pos _)).mpr (log_cost_lt large)

private theorem comparison {a b t:ℝ} (large:62208≤t) (pos:0<a) (old:a≤b*t^110) :
    a*(Real.log t)^10<b*t^115 := by
  have t0:0<t:=by linarith
  calc
    _ < a*t^5:=mul_lt_mul_of_pos_left (log_cost_lt large) pos
    _ ≤ (b*t^110)*t^5:=mul_le_mul_of_nonneg_right old (pow_nonneg t0.le _)
    _ = b*t^115:=by ring

theorem budget_of_previous {A B:ℤ}
    (old:35^5*classProduct oldCutoff .evenNoncube A B^3*classProduct oldCutoff .evenCube A B≤
      6^5*heightRadical A B^110*classProduct oldCutoff .oddCube A B^2) : Budget A B := by
  let H:=classProduct oldCutoff .evenNoncube A B
  let F:=classProduct oldCutoff .evenCube A B
  let J:=classProduct oldCutoff .oddCube A B
  let T:=heightRadical A B
  have he:0<H:=class_positive _ _ _ _
  have fe:0<F:=class_positive _ _ _ _
  have t:(62208:ℝ)≤(T:ℝ):=by exact_mod_cast radical_large A B
  have z:(35:ℝ)^5*(H:ℝ)^3*(F:ℝ)≤6^5*(T:ℝ)^110*(J:ℝ)^2:=by exact_mod_cast old
  have old':(35:ℝ)^5*(H:ℝ)^3*(F:ℝ)≤(6^5*(J:ℝ)^2)*(T:ℝ)^110:=by linarith only [z]
  have hi:=comparison t (show 0<(35:ℝ)^5*(H:ℝ)^3*(F:ℝ) by positivity) old'
  change (35:ℝ)^5*(H:ℝ)^3*(F:ℝ)*(Real.log (T:ℝ))^10≤6^5*(T:ℝ)^115*(J:ℝ)^2
  linarith only [hi]

theorem failure_log {A B:ℤ} (cop:Int.gcd A B=1) (bad:¬ChartTest A B) :
    (6:ℝ)^5*(heightRadical A B:ℝ)^115*(classProduct oldCutoff .oddCube A B:ℝ)^2 <
    35^5*(classProduct oldCutoff .evenNoncube A B:ℝ)^3*(classProduct oldCutoff .evenCube A B:ℝ)*
      (Real.log (heightRadical A B:ℝ))^10 :=
  lt_of_not_ge (fun h=>bad (chart_of_log cop h))

end
end Sun28.HeightCubics.Pooled.Logarithmic
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.log_cost_lt
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.budget_increase
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.budget_of_previous
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.failure_log
