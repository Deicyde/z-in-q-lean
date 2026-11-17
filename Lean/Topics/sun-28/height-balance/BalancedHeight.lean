import BalancedUnits

namespace Sun28.HeightBalance
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.MinimalConductors Height
open private height_div int_height from ContactHeight
noncomputable section

namespace FourRows
def heightBound (N : ℕ) : ℝ :=
  (3/2)*(128*(N:ℝ))*Real.log (128*(N:ℝ))^2+65

theorem recovery (R : FourRows) {A B d u v w : ℤ} (off : ∀ i,oldForm i A B≠0)
    (h : R.Balance A B d u v w) :
    let r := plus u v w / minus u v w
    crossRatio R.a R.b R.center A B = (1+r)^2 / (4*r) := by
  let f:=oldForm R.center A B
  have e:= (R.differences h).1
  have g:=h.first
  unfold weightA at g
  have f0 := off R.center
  have coeff := mul_ne_zero (det_ne R.ic) (det_ne R.ab)
  have uv : u^2-v^2≠0:=fun hz=>mul_ne_zero coeff f0 (by rw [←e,hz,mul_zero])
  have up : u+v≠0:= by intro hz;apply uv;linear_combination (u-v)*hz
  have um : u-v≠0:= by intro hz;apply uv;linear_combination (u+v)*hz
  have ⟨p,m⟩:=R.units off h
  have uw : u+w≠0:=by intro hz; exact p.1.1 (by simp [plus,hz])
  have hC : det R.center R.b*oldForm R.a A B*(u^2-v^2)=det R.a R.b*oldForm R.center A B*u^2 := by
    apply mul_left_cancel₀ (det_ne R.ic)
    linear_combination (u^2-v^2)*g + u^2*e
  have cq : crossRatio R.a R.b R.center A B=(u:ℚ)^2/((u:ℚ)^2-(v:ℚ)^2) := by
    unfold crossRatio
    apply (div_eq_div_iff (by exact_mod_cast mul_ne_zero (det_ne R.ab) f0)
      (by exact_mod_cast uv)).mpr
    exact_mod_cast (hC.trans (mul_comm _ _))
  have ap : (u:ℚ)+(v:ℚ)≠0:=by exact_mod_cast up
  have am : (u:ℚ)-(v:ℚ)≠0:=by exact_mod_cast um
  have aw : (u:ℚ)+(w:ℚ)≠0:=by exact_mod_cast uw
  have ratio : plus u v w / minus u v w = ((u:ℚ)+v)/((u:ℚ)-v) := by
    unfold plus minus; push_cast; field_simp [am,aw]
  dsimp only
  rw [cq,ratio]
  field_simp [ap,am,show (u:ℚ)^2-(v:ℚ)^2≠0 by exact_mod_cast uv]
  ring

/-- The height loss is absolute and uniform in every centered quadruple. -/
theorem height (published : PublishedCorollary72) (R : FourRows) {A B d u v w : ℤ}
    (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (h : R.Balance A B d u v w) :
    pairLogHeight A B ≤ 6*heightBound (primeProduct (R.primes A B))+36 := by
  let x:=plus u v w
  let y:=minus u v w
  let r:=x/y
  let H:=heightBound (primeProduct (R.primes A B))
  obtain ⟨p,m⟩:=R.units off h
  have bound (z : ℚ) (h₀ : RationalSUnit (R.primes A B) z) (h₁ : RationalSUnit (R.primes A B) (1-z)) :
      logHeight₁ z≤H := by
    have a:=(supported_corollary published (R.primes A B) (fun _=>R.primes_prime A B)
      z (1-z) h₀ h₁ (by ring)).1
    simpa only [H,heightBound,show (2:ℝ)^7=128 by norm_num] using a
  have hr : logHeight₁ r≤2*H := (height_div x y).trans
    (by linarith only [bound x p.1 p.2,bound y m.1 m.2])
  have base:=crossRatio_height R.a R.b R.center R.ab R.ia.symm R.ib.symm cop off
  have rep:=R.recovery off h
  change crossRatio R.a R.b R.center A B=(1+r)^2/(4*r) at rep
  rw [rep] at base
  have out:=height_div ((1+r)^2) (4*r)
  have den:=logHeight₁_mul_le (4:ℚ) r
  have num:=logHeight₁_add_le (1:ℚ) r
  have coeff : (totalWeight ℚ:ℝ)=1 := by rw [NumberField.totalWeight_eq_finrank];simp
  rw [coeff,one_mul,logHeight₁_one] at num
  rw [logHeight₁_pow] at out
  have four : logHeight₁ (4:ℚ)=2*Real.log 2 := by
    rw [Rat.logHeight₁_eq_log_max];norm_num
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow];norm_num
  rw [four] at den
  norm_num at out
  change pairLogHeight A B≤6*H+36
  linarith only [base,out,den,num,hr,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

end FourRows
end
end Sun28.HeightBalance
#print axioms Sun28.HeightBalance.FourRows.recovery
#print axioms Sun28.HeightBalance.FourRows.height
