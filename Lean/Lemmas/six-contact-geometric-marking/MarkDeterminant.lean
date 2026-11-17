import WeightedQuadratics
import SexticIgusaChart

/-! The covariant determinant for the specific integral rational sextic. -/
namespace ZInQBlueprint.MarkedForm
open SexticIgusaChart IntegralSextic
noncomputable section
variable {K : Type*} [Field K]

/-- Sixty times the polarized coefficients of the affine parameter sextic. -/
def coeffs (t : K) : Coeff K 6 :=
  ![480*t^2,120*t^2-360*t,24*t^2-216*t,3*t^2-96*t+81,
    -36*t+108,-10*t+90,60]

theorem coeffs_eval (t x z : K) : evalF (coeffs t) x z=60*form 1 t x z := by
  simp [coeffs,evalF,Fin.sum_univ_succ,Fin.succ,Nat.choose,form,alpha,beta,gamma]
  ring

/-- The unweighted quadratic rows before homogenizing their degrees in the sextic. -/
def baseRows (f : Coeff K 6) : Matrix (Fin 3) (Fin 3) K := ![q₁ f,q₂ f,q₃ f]

def covRows (f : Coeff K 6) : Matrix (Fin 3) (Fin 3) K := rows f

theorem homogenized_det (f : Coeff K 6) :
    (covRows f).det=(invariant f)^3*(baseRows f).det := by
  rw [Matrix.det_fin_three (covRows f),Matrix.det_fin_three (baseRows f)]
  dsimp [covRows,baseRows,rows,scale]
  ring

theorem coeffs_inv (t : K) : invariant (coeffs t)= -180*((t^2-5)^2+704) := by
  dsimp [invariant,coeffs]
  ring

def explicit1 (t : K) : Coeff K 2 :=
  ![5184*t^6 + 5184*t^5 + 362880*t^4 - 1710720*t^3 + 46656*t^2 + 3779136*t,
    1296*t^6 + 1728*t^5 + 91152*t^4 - 570240*t^3 + 2461104*t^2 + 1259712*t + 25509168,
    864*t^5 + 288*t^4 - 285120*t^3 + 1632960*t^2 + 629856*t + 17006112]

def explicit2 (t : K) : Coeff K 2 :=
  ![-746496*t^10 - 746496*t^9 - 64696320*t^8 - 363294720*t^7 - 1103321088*t^6 - 36875409408*t^5 - 52538388480*t^4 - 264841850880*t^3 - 4897760256*t^2 - 396718580736*t,
    -186624*t^10 - 248832*t^9 - 16236288*t^8 - 121098240*t^7 - 762296832*t^6 - 12291803136*t^5 - 20582014464*t^4 - 88280616960*t^3 - 319578856704*t^2 - 132239526912*t - 2677850419968,
    -124416*t^9 - 41472*t^8 - 60549120*t^7 - 324311040*t^6 - 6145901568*t^5 - 4964944896*t^4 - 44140308480*t^3 - 212236277760*t^2 - 66119763456*t - 1785233613312]

def explicit3 (t : K) : Coeff K 2 :=
  ![107495424*t^14 + 107495424*t^13 + 11107860480*t^12 + 11107860480*t^11 - 92887990272*t^10 + 347604369408*t^9 - 30522250690560*t^8 - 162268642344960*t^7 - 1552880722526208*t^6 + 253403585298432*t^5 - 12151930926366720*t^4 + 5903172481351680*t^3 + 514147280633856*t^2 + 41645929731342336*t,
    26873856*t^14 + 35831808*t^13 + 2785923072*t^12 + 3702620160*t^11 - 177567510528*t^10 + 115868123136*t^9 - 22009087881216*t^8 - 54089547448320*t^7 - 594245372792832*t^6 + 84467861766144*t^5 - 3495061309722624*t^4 + 1967724160450560*t^3 + 39974951069282304*t^2 + 13881976577114112*t + 281110025686560768,
    17915904*t^13 + 5971968*t^12 + 1851310080*t^11 - 102897008640*t^10 + 57934061568*t^9 - 9585683472384*t^8 - 27044773724160*t^7 - 137350128107520*t^6 + 42233930883072*t^5 - 304719052087296*t^4 + 983862080225280*t^3 + 26564276166082560*t^2 + 6940988288557056*t + 187406683791040512]

def explicit4 (t : K) : Coeff K 4 :=
  ![1728*t^4 + 12096*t^3 + 88128*t^2 + 699840*t,
    432*t^4 + 6768*t^3 + 32400*t^2 + 244944*t,
    72*t^4 + 3168*t^3 + 13104*t^2 + 85536*t + 52488,
    1512*t^3 + 5400*t^2 + 30456*t + 52488,
    720*t^3 + 2448*t^2 + 9072*t + 34992]

private theorem explicit_four (t : K) : quartic (coeffs t)=explicit4 t := by
  funext i; fin_cases i <;> dsimp [quartic,coeffs,explicit4] <;> ring

private theorem explicit_one (t : K) : q₁ (coeffs t)=explicit1 t := by
  unfold q₁; rw [explicit_four]
  funext i; fin_cases i <;> dsimp [contract64,coeffs,explicit4,explicit1] <;> ring

private theorem explicit_two (t : K) : q₂ (coeffs t)=explicit2 t := by
  unfold q₂; rw [explicit_four,explicit_one]
  funext i; fin_cases i <;> dsimp [contract42,explicit1,explicit4,explicit2] <;> ring

private theorem explicit_three (t : K) : q₃ (coeffs t)=explicit3 t := by
  unfold q₃; rw [explicit_four,explicit_two]
  funext i; fin_cases i <;> dsimp [contract42,explicit2,explicit4,explicit3] <;> ring

/-- All specializations, including the degenerate ones, satisfy this identity. -/
theorem coeffs_det (t : K) :
    (baseRows (coeffs t)).det=(-913008685901414400000:K)*t^7*(t^2-27)*(t^2+27)^5*
        (81*t^4+8470*t^2+59049) := by
  rw [Matrix.det_fin_three (baseRows (coeffs t))]
  unfold baseRows
  rw [explicit_one,explicit_two,explicit_three]
  simp [explicit1,explicit2,explicit3,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  ring

theorem rational_det_ne {t : ℚ} (ht : t≠0) : (covRows (coeffs t)).det ≠ 0 := by
  have n27 : ¬IsSquare (27:ℚ) := by
    change ¬ IsSquare ((27:ℕ):ℚ)
    rw [Rat.isSquare_natCast_iff]
    rintro ⟨w,hw⟩
    by_cases h : w≤5
    · nlinarith [Nat.mul_le_mul h h]
    · have g : 6≤w := by omega
      nlinarith [Nat.mul_le_mul g g]
  have s27 : t^2-27≠0 := by
    intro h
    apply n27
    refine ⟨t, ?_⟩
    nlinarith
  have pinv : (t^2-5)^2+704>0 := by positivity
  have quart : 0 < 81*t^4+8470*t^2+59049 := by positivity
  rw [homogenized_det,coeffs_inv,coeffs_det]
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) pinv.ne'))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ht)) s27)
      (pow_ne_zero _ (by positivity))) quart.ne')

theorem paper_det_ne [CharZero K] (u : ℚ) (hu : u∉ZInQ.contactSet) :
    (covRows (coeffs ((parameter u:ℚ):K))).det ≠ 0 := by
  have h := rational_det_ne (unmarked hu (one_ne_zero : (1:ℚ)≠0)).1
  rw [homogenized_det,coeffs_inv,coeffs_det] at h ⊢
  exact_mod_cast h

end
end ZInQBlueprint.MarkedForm
#print axioms ZInQBlueprint.MarkedForm.coeffs_eval
#print axioms ZInQBlueprint.MarkedForm.homogenized_det
#print axioms ZInQBlueprint.MarkedForm.coeffs_inv
#print axioms ZInQBlueprint.MarkedForm.coeffs_det
#print axioms ZInQBlueprint.MarkedForm.paper_det_ne
