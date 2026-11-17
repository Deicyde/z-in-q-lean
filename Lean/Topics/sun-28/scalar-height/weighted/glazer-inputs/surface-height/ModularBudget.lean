import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Elementary estimates in the transfer from a modular Jacobian to a quaternionic surface. -/
namespace ZInQBlueprint.FiveMetric
noncomputable section
set_option exponentiation.threshold 250

/-- The level enters through a single parameter U=C R². The field degree is allowed to grow. -/
structure ModularData (U h : ℝ) where
  genus : ℝ
  fieldDegree : ℝ
  jacHeight : ℝ
  complementHeight : ℝ
  genus_pos : 1≤genus
  genus_bound : genus≤U^2/24
  degree_pos : 1≤fieldDegree
  degree_bound : fieldDegree≤2304*U
  height_bound : jacHeight≤13000000*U^12
  isogeny_bound : h+complementHeight ≤ jacHeight+2*genus^2*(8*genus^2*Real.log (7*genus)+
      Real.log fieldDegree+Real.log (max 1 (max (Real.log fieldDegree) jacHeight)))
  lower_bound : -(3/2:ℝ)*genus ≤ complementHeight

/-- The isogeny error and the lower bound for the complementary factor cost less than
one additional U^12 apiece. All powers of U are retained. -/
theorem modular_height {U h : ℝ} (one : 1≤U) (D : ModularData U h) : h ≤ 2^24*U^12 := by
  obtain ⟨g,d,J,Z,gp,genus,dp,degree,jac,isog,low⟩:=D
  have up : 0<U:=by linarith
  have logU : Real.log U≤U:=by linarith [Real.log_le_sub_one_of_pos up]
  have pwr (a b : ℕ) (ab:a≤b) : U^a≤U^b:=pow_le_pow_right₀ one ab
  have u12 : 1≤U^12:=one_le_pow₀ one
  have lg : Real.log (7*g)≤2*U := by
    have bound : 7*g≤U^2 := by linarith only [genus,gp]
    have logh:=Real.log_le_log (by positivity : 0<7*g) bound
    rw [Real.log_pow] at logh
    norm_num only [Nat.cast_ofNat] at logh
    linarith only [logh,logU]
  have ld : Real.log d≤13*U := by
    have bound : d≤(2:ℝ)^12*U:=degree.trans (mul_le_mul_of_nonneg_right (by norm_num) up.le)
    have logh:=Real.log_le_log (by linarith : 0<d) bound
    rw [Real.log_mul (by norm_num) up.ne',Real.log_pow] at logh
    have l2:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num only [Nat.cast_ofNat] at logh
    linarith only [logh,logU,l2,one]
  have lm : Real.log (max 1 (max (Real.log d) J))≤36*U := by
    have a : (1:ℝ)≤2^24*U^12 := u12.trans (le_mul_of_one_le_left (by positivity) (by norm_num))
    have b : Real.log d≤2^24*U^12 := calc
      _ ≤ 13*U:=ld
      _ ≤ 13*U^12:=mul_le_mul_of_nonneg_left (by simpa using pwr 1 12 (by decide)) (by norm_num)
      _ ≤ _:=mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have c:=jac.trans (mul_le_mul_of_nonneg_right (by norm_num : (13000000:ℝ)≤2^24) (by positivity))
    have logh:=Real.log_le_log (by positivity : 0<max 1 (max (Real.log d) J))
      (max_le a (max_le b c))
    rw [Real.log_mul (by norm_num) (pow_pos up _).ne',Real.log_pow,Real.log_pow] at logh
    norm_num only [Nat.cast_ofNat] at logh
    linarith only [logh,logU,one,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have posg : 0≤Real.log (7*g):=Real.log_nonneg (by linarith)
  have posd : 0≤Real.log d:=Real.log_nonneg dp
  have posm : 0≤Real.log (max 1 (max (Real.log d) J)):=Real.log_nonneg (le_max_left ..)
  have e₁ : 16*g^4*Real.log (7*g)≤(32/24^4)*U^9 := calc
    _ ≤ 16*(U^2/24)^4*(2*U) := by
      gcongr
    _ = _ := by ring
  have e₂ : 2*g^2*(Real.log d+Real.log (max 1 (max (Real.log d) J)))≤(98/24^2)*U^5 := calc
    _ ≤ 2*(U^2/24)^2*(49*U) := by
      have a : Real.log d+Real.log (max 1 (max (Real.log d) J))≤49*U:=by linarith only [ld,lm]
      gcongr
    _ = _ := by ring
  have e : (32/24^4)*U^9+(98/24^2)*U^5 ≤ U^12 := by
    have a:=mul_le_mul_of_nonneg_left (pwr 9 12 (by decide)) (by norm_num : (0:ℝ)≤32/24^4)
    have b:=mul_le_mul_of_nonneg_left (pwr 5 12 (by decide)) (by norm_num : (0:ℝ)≤98/24^2)
    linarith only [a,b,show (0:ℝ)≤U^12 by positivity]
  have lower : -U^12 ≤ Z := by linarith only [low,genus,pwr 2 12 (by decide),u12]
  calc
    h ≤ J + (16*g^4*Real.log (7*g)) + 2*g^2*(Real.log d+Real.log (max 1 (max (Real.log d) J)))-Z := by
      linear_combination isog
    _ ≤ 2^24*U^12 := by linarith only [jac,lower,e₁,e₂,e,u12]

/-- The CM branch uses the surface isogeny estimate and a CM elliptic factor of height at most 3R. -/
theorem cm_height {R h : ℝ} (one:1≤R)
    (estimate:h≤6*R+8*Real.log (14^32*576*max 1 (max (Real.log 576) (6*R)))) : h≤6^100*R^24 := by
  have rp : 0<R:=by linarith
  have ld:Real.log 576≤576:=by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<576)]
  have top : max 1 (max (Real.log 576) (6*R))≤576*R := by
    exact max_le (by linarith) (max_le (by linarith) (by linarith))
  have zpos : 0<14^32*576*max 1 (max (Real.log 576) (6*R)) := by positivity
  have logbound := (Real.log_le_sub_one_of_pos zpos).trans
    (sub_le_self _ (by norm_num : (0:ℝ)≤1))
  have cap := mul_le_mul_of_nonneg_left top (by norm_num : (0:ℝ)≤14^32*576)
  have h' : h≤6*R+8*(14^32*576*(576*R)) := by
    exact estimate.trans (by gcongr; exact logbound.trans cap)
  have growth : R≤R^24 := by simpa using pow_le_pow_right₀ one (show 1≤24 by decide)
  calc h ≤ _ := h'
       _ = (6+8*14^32*576^2)*R := by ring
       _ ≤ 6^100*R := mul_le_mul_of_nonneg_right (by norm_num) rp.le
       _ ≤ _ := mul_le_mul_of_nonneg_left growth (by positivity)

end
end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.modular_height
#print axioms ZInQBlueprint.FiveMetric.cm_height
