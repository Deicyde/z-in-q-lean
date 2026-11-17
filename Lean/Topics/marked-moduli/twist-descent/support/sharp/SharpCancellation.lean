import MordellSupport

/-! Exact cancellation in the two rescaled primitive Mordell models. -/
namespace ZInQBlueprint.TwistDescent
open ZInQ ZInQBlueprint.OddSupport UniqueFactorizationMonoid

/-- The cube of the cancelled gcd divides c². -/
theorem cancellation_cube_dvd {Z k w v c : ℕ} (cop : w.Coprime v) (cube : k^3∣w)
    (eqn : Z^3=(c*v)^2+27*w^2) : ((k^2).gcd Z)^3 ∣ c^2 := by
  let g := (k^2).gcd Z
  have gk : g ∣ k^2 := Nat.gcd_dvd_left _ _
  have gz : g ∣ Z := Nat.gcd_dvd_right _ _
  have gw : g ∣ w := gk.trans ((pow_dvd_pow k (by decide : 2≤3)).trans cube)
  have gw₂ : g^3 ∣ w^2 := by
    have gg := pow_dvd_pow_of_dvd gk 3
    have ww := pow_dvd_pow_of_dvd cube 2
    rw [←pow_mul] at gg ww
    exact gg.trans ww
  have sub := pow_dvd_pow_of_dvd gz 3
  rw [eqn] at sub
  have cv := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right gw₂ 27)).mpr sub
  rw [mul_pow] at cv
  have no := ((Nat.Coprime.of_dvd_left gw cop).pow_left 3).pow_right 2
  exact no.dvd_mul_right.mp cv

/-- P supplies the rescaling. The gcd divides nine. -/
theorem real_cubic_cancellation {P Q T k : ℕ} (cop : P.Coprime Q) (cube : k^3∣P)
    (norm : P^2+27*Q^2=T^3) : (k^2).gcd (3*T) ∣ 9 := by
  have model : (3*T)^3=(27*Q)^2+27*P^2 := by nlinarith only [norm]
  exact (pow_dvd_pow_iff_dvd (by decide : (3:ℕ)≠0)).1
    (show ((k^2).gcd (3*T))^3 ∣ 9^3 from cancellation_cube_dvd cop cube model)

/-- Q supplies the rescaling. No factor cancels. -/
theorem imaginary_cubic_cancellation {P Q T k : ℕ} (cop : P.Coprime Q) (cube : k^3∣Q)
    (norm : P^2+27*Q^2=T^3) : (k^2).gcd T = 1 := by
  have model : T^3=(1*P)^2+27*Q^2 := by simpa using norm.symm
  have h : ((k^2).gcd T)^3 ∣ 1^3 := cancellation_cube_dvd cop.symm cube model
  exact Nat.dvd_one.mp ((pow_dvd_pow_iff_dvd (by decide : (3:ℕ)≠0)).1 h)

/-- The exact factor in recovering the original integral numerator. -/
theorem scaled_numerator_exact (Z : ℕ) {k : ℕ} (kp : 0<k) :
    Z=(((Z:ℚ)/(k:ℚ)^2).num.natAbs) * (k^2).gcd Z := by
  have q : ((Z:ℚ)/(k:ℚ)^2)=mkRat (Z:ℤ) (k^2) := by
    rw [←Rat.divInt_ofNat,Rat.divInt_eq_div]
    push_cast
    rfl
  rw [q,Rat.num_mkRat]
  simp [kp.ne']
  rw [←Int.natCast_ediv]
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_right (k^2) Z)).symm

/-- The unreduced numerator Z can lose a factor of at most nine for any 1≤c≤27.
This includes both actual models and needs no published height theorem. -/
theorem numerator_loss_nine {Z k w v c : ℕ} (kp : 0<k) (cop : w.Coprime v)
    (cp : 0<c) (bound : c≤27) (cube : k^3∣w) (eqn : Z^3=(c*v)^2+27*w^2) :
    Z ≤ 9*(((Z:ℚ)/(k:ℚ)^2).num.natAbs) := by
  have h := Nat.le_of_dvd (pow_pos cp 2) (cancellation_cube_dvd cop cube eqn)
  have p : ((k^2).gcd Z)^3 ≤ 9^3 := h.trans (Nat.pow_le_pow_left bound 2)
  have small : (k^2).gcd Z ≤ 9 := by
    by_contra! no
    have := Nat.pow_le_pow_left (show 10≤(k^2).gcd Z by omega) 3
    omega
  calc
    Z = _ := scaled_numerator_exact Z kp
    _ ≤ 9*(((Z:ℚ)/(k:ℚ)^2).num.natAbs) := by rw [mul_comm]; gcongr

/-- The primitive point (x,y)=(6,3) on the twist d=21 attains the loss. -/
theorem cancellation_nine_attained :
    Squarefree (21:ℤ) ∧ 30*(21:ℚ)*3^2=quintic 6 ∧
    realCubic 6 1=162 ∧ imaginaryCubic 6 1=35 ∧ quadraticNorm 6 1=39 ∧
    (162:ℕ).Coprime 35 ∧ (162:ℕ)^2+27*35^2=39^3 ∧ (3:ℕ)^3∣162 ∧
    ((3:ℕ)^2).gcd (3*39)=9 ∧ ((3*(39:ℚ))/3^2).num=13 ∧ (3*(39:ℕ))=9*13 := by
  constructor
  · apply Int.squarefree_natAbs.mp
    change Squarefree (3*7 : ℕ)
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 7)).2
      ⟨(by decide : Nat.Prime 3).squarefree,(by decide : Nat.Prime 7).squarefree⟩
  · norm_num [quintic,realCubic,imaginaryCubic,quadraticNorm]

#print axioms cancellation_cube_dvd
#print axioms real_cubic_cancellation
#print axioms imaginary_cubic_cancellation
#print axioms scaled_numerator_exact
#print axioms numerator_loss_nine
#print axioms cancellation_nine_attained
end ZInQBlueprint.TwistDescent
