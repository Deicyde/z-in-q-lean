import DoubleVanishing
import PreparedExample
import FiniteScalarPole

/-! Infinitely many prepared scalar squareclasses have an explicit certificate with
both ordinates zero on the negative companion. The tree value is specified as a rational. -/
namespace Sun28.MultiplierChoice
open Sun28.Ordinary Sun28.ScalarHeight Sun28.FixedPreparation Sun28.ContactFactors
  Sun28.PreparedPoles Sun28.TwistRank Sun28.FinitePole
noncomputable section
set_option maxRecDepth 8192

def base : ℕ := 526361
private def C : ℕ := gamma
private def scaleK (n:ℕ) : ℕ := 3*base*C^2*(n+2)+1
private def divisorK (n:ℕ) : ℕ := (scaleK n)^2-3*base*C^2
def scalarPole (n:ℕ) : ℚ :=
  15*(base:ℚ)*(2*(C:ℚ)*(scaleK n:ℚ)/(divisorK n:ℚ))^2

private theorem positive_K (n:ℕ) : 0<scaleK n := by unfold scaleK;omega
private theorem big_K (n:ℕ) : 3*base*C^2<scaleK n := by
  unfold scaleK
  nlinarith only [Nat.zero_le (3*base*C^2*n)]
private theorem normalizer (n:ℕ) : (divisorK n:ℚ)=(scaleK n:ℚ)^2-3*(base:ℚ)*(C:ℚ)^2 := by
  have e:=big_K n
  have low:3*base*C^2≤(scaleK n)^2:=by exact e.le.trans (Nat.le_self_pow (by decide : 2≠0) (scaleK n))
  simp only [divisorK,Nat.cast_sub low,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
private theorem div_positive (n:ℕ) : 0<(divisorK n:ℚ) := by
  rw [normalizer]
  have e : 3*(base:ℚ)*(C:ℚ)^2<(scaleK n:ℚ):=by exact_mod_cast big_K n
  have k : 1≤(scaleK n:ℚ):=by exact_mod_cast positive_K n
  nlinarith only [e,k,mul_nonneg (sub_nonneg.mpr k) (le_trans zero_le_one k)]

private theorem div_residue {p:ℕ} (prime:p.Prime) (d:p∣3*base*C^2) (n:ℕ) : ¬p∣divisorK n := by
  intro h
  have one : divisorK n+3*base*C^2= (scaleK n)^2:=by
    apply Nat.sub_add_cancel
    have e:=big_K n
    exact e.le.trans (Nat.le_self_pow (by decide : 2≠0) (scaleK n))
  have div:p∣(scaleK n)^2:=one ▸ dvd_add h d
  have neg:¬p∣scaleK n:=fun h=>by
    have h1:p∣1:=by
      change p∣3*base*C^2*(n+2)+1 at h
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_left d _)).mp h
    exact prime.not_dvd_one h1
  exact neg (prime.dvd_of_dvd_pow div)

private theorem form_bound (n:ℕ) : 0<scalarPole n ∧ scalarPole n<1/2 := by
  let x:ℚ:=scaleK n
  let t:ℚ:=3*(base:ℚ)*(C:ℚ)^2
  have large:(1:ℚ)<t:=by norm_num [t,base,C,gamma,FixedPreparation.primorial]
  have xeq:x=t*(n+2)+1:=by dsimp [x,t,scaleK];push_cast;ring
  have xBig: 1200000 < x := by
    have big:(1200000:ℚ)<2*t:=by norm_num [t,base,C,gamma,FixedPreparation.primorial]
    nlinarith only [xeq,big,mul_nonneg (le_trans (by norm_num) large.le) (Nat.cast_nonneg n)]
  have tx:t<x:=by dsimp [t,x];exact_mod_cast big_K n
  have xp:0<x:=by linarith
  have dd:0<x^2-t:=lt_trans (by norm_num : (0:ℚ)<1) (by nlinarith only [xBig,tx,mul_self_nonneg (x-1)])
  have edge : x^2/2 < x^2-t:=by nlinarith only [tx,xBig,mul_nonneg (sub_nonneg.mpr (show (2:ℚ)≤x by linarith)) xp.le]
  have tpos:0<t:=by linarith
  have tail: 40*t*x^2 < (x^2-t)^2 := by
    have cap: 160*t < x^2 :=by nlinarith only [tx,xBig,mul_nonneg (sub_nonneg.mpr (show (160:ℚ)≤x by linarith)) xp.le]
    have v:=mul_lt_mul_of_pos_right cap (sq_pos_of_pos xp)
    have e:=sq_lt_sq' (by nlinarith only [dd,sq_nonneg x]: -(x^2-t)<x^2/2) edge
    nlinarith only [v,e]
  have cc:0<(C:ℚ):=by norm_num [C,gamma,FixedPreparation.primorial]
  have bb:0<(base:ℚ):=by norm_num [base]
  unfold scalarPole
  rw [normalizer]
  change 0<15*(base:ℚ)*(2*(C:ℚ)*x/(x^2-t))^2 ∧ _
  constructor
  · positivity
  · change 15*(base:ℚ)*(2*(C:ℚ)*x/(x^2-t))^2 < 1/2
    rw [div_pow]
    dsimp [t] at tail
    field_simp [dd.ne']
    nlinarith only [tail]

theorem negative_companion (n:ℕ) : DoubleRoot (-5) (scalarPole n) := by
  obtain ⟨bp,_⟩:=form_bound n
  apply (double_root_iff (by norm_num) bp.ne' (by linarith)).mpr
  left
  refine ⟨((scaleK n:ℚ)^2+3*(base:ℚ)*(C:ℚ)^2)/(divisorK n:ℚ),?_⟩
  have nz: (divisorK n:ℚ)≠0:=(div_positive n).ne'
  unfold scalarPole
  field_simp [nz]
  rw [normalizer]
  ring

theorem scalar_trace_value (n:ℕ) : ∃ W:ℚ,W≠0 ∧
    signedValue (scalarRadicand (beta 0)) (-1) gamma denominator W=scalarPole n := by
  let w:ℚ:=(scaleK n:ℚ)*(1+(denominator:ℚ)*31581660^2)/(divisorK n:ℚ)
  have d:0<(divisorK n:ℚ):=div_positive n
  have k:0<(scaleK n:ℚ):=by exact_mod_cast positive_K n
  have rad:scalarRadicand (beta 0)= -31581660:=by norm_num [scalarRadicand,beta]
  refine ⟨w,(show 0<w by dsimp [w];positivity).ne',?_⟩
  rw [rad]
  unfold signedValue scalarPole w
  dsimp [C,base]
  have front : (1:ℚ)+(denominator:ℚ)*31581660^2≠0:=by positivity
  field_simp [d.ne',front]
  ring

private theorem val_divisor (p n:ℕ) [pp:Fact p.Prime] (dvd:p∣3*base*C^2) :
    padicValRat p (divisorK n:ℚ)=0 := by
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd (div_residue pp.out dvd n)];rfl

private theorem scalar_den (n:ℕ) : IsSquare (scalarPole n).den := by
  apply ZInQ.Mult.isSquare_den_of_even
  intro p pp neg
  let _ : Fact p.Prime:=⟨pp⟩
  let L:ℕ:=15*base
  have lp:0<(L:ℚ):=by norm_num [L,base]
  let v:ℕ:=2*C*scaleK n
  have vp:0<(v:ℚ):=by
    have k:0<(scaleK n:ℚ):=by exact_mod_cast positive_K n
    dsimp [v];push_cast;have : (0:ℚ)<C:=by norm_num [C,gamma,FixedPreparation.primorial]
    positivity
  have repr:scalarPole n=(L:ℚ)*((v:ℚ)/(divisorK n:ℚ))^2:=by unfold scalarPole;dsimp [L,v];push_cast;ring
  have dn:=div_positive n
  rw [repr,padicValRat.mul lp.ne' (pow_ne_zero 2 (div_ne_zero vp.ne' dn.ne')),padicValRat.pow,
    padicValRat.div vp.ne' dn.ne']
  by_cases hit:p∣L
  · have dvd:p∣3*base*C^2:=hit.trans (show L∣3*base*C^2 by decide)
    have d0:=val_divisor p n dvd
    rw [repr,padicValRat.mul lp.ne' (pow_ne_zero 2 (div_ne_zero vp.ne' dn.ne')),padicValRat.pow,
      padicValRat.div vp.ne' dn.ne',d0,sub_zero] at neg
    have h₁:=zero_le_padicValRat_of_nat (p:=p) L
    have h₂:=zero_le_padicValRat_of_nat (p:=p) v
    omega
  · rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd hit]
    exact ⟨(padicValRat p (v:ℚ)-padicValRat p (divisorK n:ℚ)),by push_cast;ring⟩

private theorem scalar_depth (n p:ℕ) (mem:p∈primes) : 4≤padicValRat p (scalarPole n) := by
  have pp:Nat.Prime p:=(show ∀ p∈primes,Nat.Prime p by decide) p mem
  let _:Fact p.Prime:=⟨pp⟩
  have dvd:p∣3*base*C^2:=(show ∀ p∈primes,p∣3*base*C^2 by decide) p mem
  have vp:padicValRat p (C:ℚ)=2:=fixed_gamma_order p mem
  have kn:0<(scaleK n:ℚ):=by exact_mod_cast positive_K n
  have dn:=div_positive n
  have cc:0<(C:ℚ):=by norm_num [C,gamma,FixedPreparation.primorial]
  have bb:0<(base:ℚ):=by norm_num [base]
  have t0:=val_divisor p n dvd
  have lp:0≤padicValRat p ((15:ℚ)*base):=by exact_mod_cast (zero_le_padicValRat_of_nat (p:=p) (15*base))
  have two:0≤padicValRat p (2:ℚ):=by exact_mod_cast (zero_le_padicValRat_of_nat (p:=p) 2)
  have vv:=zero_le_padicValRat_of_nat (p:=p) (scaleK n)
  unfold scalarPole
  rw [padicValRat.mul (mul_pos (by norm_num) bb).ne' (pow_ne_zero 2 (div_ne_zero (mul_pos (mul_pos (by norm_num) cc) kn).ne' dn.ne')),
    padicValRat.pow,padicValRat.div (mul_pos (mul_pos (by norm_num) cc) kn).ne' dn.ne',
    padicValRat.mul (mul_pos (by norm_num) cc).ne' kn.ne',padicValRat.mul (by norm_num) cc.ne',vp,t0]
  omega

theorem prepared_family (n:ℕ) : ClassPrepared (scalarPole n) ∧
    polePredicate smallMultipliers (scalarPole n) := by
  obtain ⟨pos,small⟩:=form_bound n
  refine ⟨⟨⟨scalar_den n,pos,small,scalar_depth n⟩,?_⟩,Or.inr ⟨-5,(by decide),double_accepted (negative_companion n)⟩⟩
  intro m b d mem c
  obtain ⟨W,_,E⟩:=scalar_trace_value n
  rw [←E] at c pos
  have rad:(-1:ℚ)*scalarRadicand (beta ((0:ℤ):ℚ))=((integerRadicand 0).natAbs:ℚ):=by
    norm_num [integerRadicand,scalarRadicand,beta]
  obtain ⟨positive,classEq⟩:=scalar_class (X:=0) c pos rad
  exact Or.inr ⟨0,m,positive,mem,classEq⟩

end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.negative_companion
#print axioms Sun28.MultiplierChoice.scalar_trace_value
#print axioms Sun28.MultiplierChoice.prepared_family
