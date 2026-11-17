import HeightEquivalence
import Mathlib.Data.ZMod.Basic

/-! Three integral forms obtained by cubing a + b√(-3). -/
namespace ZInQBlueprint.TwistDescent
open ZInQ ZInQBlueprint.OddSupport

def realCubic (a b : ℤ) : ℤ := a*(a^2-9*b^2)
def imaginaryCubic (a b : ℤ) : ℤ := b*(a^2-b^2)
def quadraticNorm (a b : ℤ) : ℤ := a^2+3*b^2

theorem cubic_identity (a b : ℤ) :
    realCubic a b ^ 2 + 27 * imaginaryCubic a b ^ 2 = quadraticNorm a b ^ 3 := by
  unfold realCubic imaginaryCubic quadraticNorm
  ring

theorem product_at_twist {d : ℤ} {x y : ℚ} (point : 30*(d:ℚ)*y^2=quintic x) :
    (realCubic x.num x.den:ℚ)*(imaginaryCubic x.num x.den:ℚ) =
      30*(d:ℚ)*(y*(x.den:ℚ)^3)^2 := by
  have h : (x.num:ℚ) = x*(x.den:ℚ) := (div_eq_iff (by exact_mod_cast x.den_nz)).mp x.num_div_den
  unfold realCubic imaginaryCubic
  push_cast
  rw [h]
  unfold quintic at point
  linear_combination -(x.den:ℚ)^6*point

theorem prime_dvd_both {a b : ℤ} (hab : a.natAbs.Coprime b.natAbs) {p : ℕ} (hp : p.Prime)
    (hA : (p:ℤ) ∣ realCubic a b) (hB : (p:ℤ) ∣ imaginaryCubic a b) : p=2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have noCommon : ¬ ((a:ZMod p)=0 ∧ (b:ZMod p)=0) := by
    rintro ⟨ha,hb⟩
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha)),
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb))⟩) hab
  have ha := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hA
  have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hB
  simp only [realCubic,imaginaryCubic,Int.cast_mul,Int.cast_sub,Int.cast_pow,Int.cast_ofNat] at ha hb
  rcases mul_eq_zero.mp ha with za|qa
  · rw [za] at hb
    simp at hb
    exact (noCommon ⟨za,by aesop⟩).elim
  rcases mul_eq_zero.mp hb with zb|qb
  · simp [zb] at qa
    exact (noCommon ⟨qa,zb⟩).elim
  have nb : (b:ZMod p)≠0 := by
    intro h
    simp [h] at qb
    exact noCommon ⟨qb,h⟩
  have zero : (8:ZMod p)*(b:ZMod p)^2=0 := by linear_combination qb-qa
  have zero8 := (mul_eq_zero.mp zero).resolve_right (pow_ne_zero _ nb)
  have pd : p ∣ 8 := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using zero8 : ((8:ℕ):ZMod p)=0)
  exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp
    (hp.dvd_of_dvd_pow (n:=3) (by simpa only [show (2:ℕ)^3=8 by decide] using pd))

#print axioms cubic_identity
#print axioms product_at_twist
#print axioms prime_dvd_both
end ZInQBlueprint.TwistDescent
