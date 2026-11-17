import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Sun28.TwistPrimes

/-- At a prime away from 6β, splitting gives a unit root of β. -/
def SplitRoot (β p : ℕ) : Prop :=
  p.Prime ∧ ¬ p∣6*β ∧ ∃ r : ℕ, r^2 ≡ β [MOD p]

def SimpleRoot (β p r : ℕ) : Prop :=
  r^2 ≡ β [MOD p] ∧ ¬ r^2 ≡ β [MOD p^2]

theorem simple_root {β p : ℕ} (h : SplitRoot β p) :
    ∃ r, SimpleRoot β p r := by
  obtain ⟨pp,good,r,root⟩ := h
  by_cases deep : r^2 ≡ β [MOD p^2]
  · have er : r+p ≡ r [MOD p] := by simp [Nat.ModEq]
    refine ⟨r+p,(er.pow 2).trans root,?_⟩
    intro next
    have difference := ((next.trans deep.symm).symm).dvd
    push_cast at difference
    obtain ⟨q,eq⟩ := difference
    have pn : (p:ℤ)≠0 := by exact_mod_cast pp.ne_zero
    have canceled : 2*(r:ℤ)+(p:ℤ) = p*q := by
      apply mul_left_cancel₀ pn
      linear_combination eq
    have divides : (p:ℤ)∣2*(r:ℤ) := ⟨q-1,by linear_combination canceled⟩
    have small : p∣2*r := by exact_mod_cast divides
    rcases pp.dvd_mul.mp small with d | d
    · exact good (d.trans ⟨3*β,by ring⟩)
    · have db : p∣β := (root.dvd_iff (dvd_refl p)).mp (dvd_pow d (by decide : 2≠0))
      exact good (dvd_mul_of_dvd_right db 6)
  · exact ⟨r,root,deep⟩

/-- A prime forced to order one in the first factor is absent from the
second, and survives removal of squares in their product. -/
theorem forced_factor {β k p θ h : ℕ} (hk : β<k^2) (hp : SplitRoot β p)
    (simple : SimpleRoot β p k)
    (eq : (k^2-β)*(9*k^2-β) = θ*h^2) : p∣θ ∧ ¬p∣h := by
  let : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨shallow,deep⟩ := simple
  have hf : p∣k^2-β := (Nat.modEq_iff_dvd' hk.le).mp shallow.symm
  have hf2 : ¬p^2∣k^2-β := fun d => deep ((Nat.modEq_iff_dvd' hk.le).mpr d).symm
  have N : β≤9*k^2 := by omega
  have hg : ¬p∣9*k^2-β := by
    intro div
    have e := (ZMod.natCast_eq_natCast_iff _ _ _).mpr shallow
    push_cast at e
    have z := (ZMod.natCast_eq_zero_iff _ _).mpr div
    rw [Nat.cast_sub N,Nat.cast_mul,Nat.cast_pow,e] at z
    have kill : 8*(β:ZMod p)=0 := by linear_combination z
    have bad : p∣8*β := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using kill)
    rcases hp.1.dvd_mul.mp bad with d | d
    · have alt : p∣2^3 := d
      exact hp.2.1 ((hp.1.dvd_of_dvd_pow alt).trans ⟨3*β,by ring⟩)
    · exact hp.2.1 (dvd_mul_of_dvd_right d 6)
  have val1 : padicValNat p (k^2-β)=1 := by
    have lo : 1≤padicValNat p (k^2-β) := one_le_padicValNat_of_dvd (Nat.sub_ne_zero_of_lt hk) hf
    have hi := (padicValNat_dvd_iff_le (by omega : k^2-β≠0)).not.mp hf2
    omega
  have pos : 0<θ*h^2 := eq ▸ Nat.mul_pos (Nat.sub_pos_of_lt hk) (Nat.sub_pos_of_lt (by omega : β<9*k^2))
  have nt : θ≠0 := by rintro rfl; simp at pos
  have nh : h≠0 := by rintro rfl; simp at pos
  have vals := congrArg (padicValNat p) eq
  rw [padicValNat.mul (by omega) (by omega),val1,padicValNat.eq_zero_of_not_dvd hg,
    padicValNat.mul nt (pow_ne_zero _ nh),padicValNat.pow] at vals
  have theta_val : padicValNat p θ=1 := by omega
  have hval : padicValNat p h=0 := by omega
  exact ⟨padicValNat.dvd_of_ne_zero (by omega), fun d => by
    exact ((dvd_iff_padicValNat_ne_zero nh).mp d) hval⟩

/-- A Euclidean construction of arbitrarily large split primes, with an
explicit modular square root built from a factorial. -/
theorem fresh_split {β : ℕ} (hb : 0<β) (B : ℕ) :
    ∃ p : ℕ, B<p ∧ SplitRoot β p := by
  let t := 6*B.factorial
  have tp : 6≤t := by have := Nat.factorial_pos B; dsimp [t]; omega
  have two : 2<β*t^2 := by
    have z : 1*6^2≤β*t^2 := Nat.mul_le_mul hb (Nat.pow_le_pow_left tp 2)
    omega
  let M := β*t^2-1
  have em : M+1=β*t^2 := Nat.sub_add_cancel (by omega)
  obtain ⟨p,pp,hp⟩ := Nat.exists_prime_and_dvd (show M≠1 by omega)
  have unit : ¬p∣β*t^2 := by
    intro d
    have diff : p∣M+1 := em ▸ d
    exact pp.not_dvd_one ((Nat.dvd_add_iff_right (n:=1) hp).mpr diff)
  have dn : ¬p∣t := fun d => unit (dvd_mul_of_dvd_right (dvd_pow d (by decide : 2≠0)) β)
  have db : ¬p∣β := fun d => unit (dvd_mul_of_dvd_left d (t^2))
  refine ⟨p,?_,pp,?_,β*t,?_⟩
  · by_contra! le
    exact dn (dvd_mul_of_dvd_right (Nat.dvd_factorial pp.pos le) 6)
  · intro d
    exact (pp.dvd_mul.mp d).elim (fun d6 => dn (dvd_mul_of_dvd_left d6 _)) db
  · have congr : β*t^2 ≡ 1 [MOD p] := (Nat.modEq_iff_dvd' (by omega : 1≤β*t^2)).mpr hp |>.symm
    rw [show (β*t)^2=β*(β*t^2) by ring]
    simpa only [Nat.mul_one] using congr.mul_left β

end Sun28.TwistPrimes
#print axioms Sun28.TwistPrimes.simple_root
#print axioms Sun28.TwistPrimes.forced_factor
#print axioms Sun28.TwistPrimes.fresh_split
