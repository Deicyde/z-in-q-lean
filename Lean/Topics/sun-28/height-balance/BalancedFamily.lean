import BalancedSector
import Mathlib.NumberTheory.PrimesCongruentOne

namespace Sun28.HeightBalance
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.MinimalConductors Sun28.HeightFibres Height
open Sun28.HeightFibres.Sharp
noncomputable section
namespace Family

def rows : FourRows := ⟨0,1,2,3,by decide,by decide,by decide,by decide,by decide,by decide⟩
def U (t : ℤ) := 2401*t^2-1
def V (t : ℤ) := 2401*t^2-2*t+1
def W (t : ℤ) := -2401*t^2+4802*t-1
def A (t : ℤ) := U t^2
def B (t : ℤ) := 4*t*(t-1)*(2401*t-1)

/-- An actual degree-four rational family on the chart with center at infinity. -/
theorem balanced (t : ℤ) : rows.Balance (A t) (B t) 1 (U t) (V t) (W t) := by
  constructor
  · change 1*A t=1*U t^2; rfl
  · change 1*(A t-B t)=1*V t^2; unfold A B U V; ring
  · change 1*(A t-2401*B t)=1*W t^2; unfold A B U W; ring

theorem primitive {t : ℤ} (m : (2400:ℤ)∣t) : Int.gcd (A t) (B t)=1 := by
  apply Int.isCoprime_iff_gcd_eq_one.mp
  have cp : IsCoprime (2401*t^2-1) (2401*t^2-2*t+1) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    by_contra no
    obtain ⟨q,hq,d₁,d₂⟩:=Nat.Prime.not_coprime_iff_dvd.mp no
    let p : ℤ := q
    have hp:Prime p:=by simpa [p,Int.prime_iff_natAbs_prime] using hq
    have hu:p∣2401*t^2-1:=Int.natAbs_dvd_natAbs.mp (by simpa [p] using d₁)
    have hv:p∣2401*t^2-2*t+1:=Int.natAbs_dvd_natAbs.mp (by simpa [p] using d₂)
    have h₂ : p∣2*(t-1) := by convert (dvd_sub hu hv) using 1; ring
    rcases hp.dvd_or_dvd h₂ with two|tm
    · have pt : p∣t:=(two.trans (show (2:ℤ)∣2400 by decide)).trans m
      have one : p∣1 := by convert dvd_sub (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left pt t) (2401:ℤ)) hu using 1; ring
      exact hp.not_isUnit (isUnit_iff_dvd_one.mpr one)
    · have pf : p∣(2400:ℤ) := by
        convert dvd_sub hu (dvd_mul_of_dvd_left tm (2401*(t+1))) using 1; ring
      have pt := pf.trans m
      have one : p∣1 := by convert dvd_sub pt tm using 1; ring
      exact hp.not_isUnit (isUnit_iff_dvd_one.mpr one)
  obtain ⟨a,b,hab⟩:=cp.pow_left (m:=2) |>.pow_right (n:=2)
  refine ⟨a+b,-b,?_⟩
  change a*(U t)^2+b*(V t)^2=1 at hab
  have diff : V t^2=A t-B t:=by unfold V A U B;ring
  rw [diff] at hab
  change (a+b)*A t+-b*B t=1
  change a*A t+b*(A t-B t)=1 at hab
  linear_combination hab

private theorem positive {t : ℤ} (large : 100≤t) :
    0<B t ∧ 0<A t ∧ 0<V t ∧ W t<0 := by
  have sq : 3*t≤t^2:= by nlinarith [mul_nonneg (by omega : 0≤t-3) (by omega : 0≤t)]
  refine ⟨?_,?_,?_,?_⟩
  · unfold B;exact mul_pos (mul_pos (mul_pos (by norm_num) (by omega)) (by omega)) (by omega)
  · unfold A U; exact sq_pos_of_pos (by nlinarith)
  · unfold V; linarith
  · unfold W; linarith

theorem off_marks {t:ℤ} (ht:100≤t) : ∀ i,oldForm i (A t) (B t)≠0 := by
  obtain ⟨pb,pa,pv,pw⟩:=positive ht
  have x:= (balanced t).second
  have y:= (balanced t).third
  change 1*(A t-B t)=1*(V t)^2 at x
  change 1*(A t-2401*B t)=1*(W t)^2 at y
  have vv := sq_pos_of_pos pv
  have ww := sq_pos_of_ne_zero (ne_of_lt pw)
  intro i
  fin_cases i
  · exact pb.ne'
  · exact pa.ne'
  · change A t-B t≠0; linarith
  · change A t-2401*B t≠0; linarith
  · change 32*A t+343*B t≠0; linarith

end Family
end
end Sun28.HeightBalance
#print axioms Sun28.HeightBalance.Family.balanced
#print axioms Sun28.HeightBalance.Family.primitive
#print axioms Sun28.HeightBalance.Family.off_marks
