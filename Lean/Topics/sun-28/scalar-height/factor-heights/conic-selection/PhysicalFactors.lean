import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas

namespace Sun28.ConicSelection
set_option maxHeartbeats 1000000
set_option linter.unnecessarySimpa false

structure Factors (s : ℚ) where
  a : ℤ
  b : ℤ
  P : ℤ
  Q : ℤ
  A7 : ℤ
  A16 : ℤ
  cop : a.natAbs.Coprime b.natAbs
  bpos : 0 < b
  odd7 : ¬ (7 : ℤ) ∣ b
  slope : s * (b : ℚ)^2 = (a : ℚ)^2
  mark7 : 7*(a^2-4*b^2) = A7^2
  mark16 : 16*a^2-15*b^2 = A16^2
  Ppos : 0 < P
  Qpos : 0 < Q
  diff : Q-P = 686*a^2-349*b^2
  prod : P*Q = 7194*b^4

theorem physical_factors {s y r v w : ℚ} (rng : 4<s) (sr : s=r^2)
    (sa : 7*(s-4)=v^2) (sb : 16*s-15=w^2)
    (curve : y^2=s*(s-4)*(16*s-15)*(1372*s^2-1396*s+439)) : Nonempty (Factors s) := by
  let a:=r.num
  let b:ℤ:=r.den
  let M:=686*a^2-349*b^2
  have cop : a.natAbs.Coprime b.natAbs := by simpa [a,b] using r.reduced
  have bp : 0<b := by dsimp [b]; exact_mod_cast r.den_pos
  have bn : (b:ℚ)≠0 := by exact_mod_cast bp.ne'
  have ar : (a:ℚ)=r*b := by
    exact (div_eq_iff bn).mp (by simpa [a,b] using r.num_div_den)
  have sl : s*(b:ℚ)^2=(a:ℚ)^2 := by rw [ar,sr]; ring
  have eq7 : IsSquare (((7*(a^2-4*b^2):ℤ):ℚ)) := by
    refine ⟨v*b,?_⟩; push_cast; rw [←sl]; linear_combination (b:ℚ)^2*sa
  have eq16 : IsSquare (((16*a^2-15*b^2:ℤ):ℚ)) := by
    refine ⟨w*b,?_⟩; push_cast; rw [←sl]; linear_combination (b:ℚ)^2*sb
  obtain ⟨A,hA⟩:=Rat.isSquare_intCast_iff.mp eq7
  obtain ⟨B,hB⟩:=Rat.isSquare_intCast_iff.mp eq16
  rw [←sq] at hA hB
  have ip := Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 7)
  have odd7 : ¬ (7:ℤ)∣b := by
    intro hb
    have pA : (7:ℤ)∣A := ip.dvd_of_dvd_pow (n:=2) (hA ▸ dvd_mul_right ..)
    obtain ⟨k,hk⟩:=pA
    have ma : a^2-4*b^2=7*k^2 := by rw [hk] at hA; linarith only [show 7*(a^2-4*b^2)=49*k^2 by linear_combination hA]
    have pa : (7:ℤ)∣a^2 := by
      obtain ⟨l,hl⟩:=hb; refine ⟨k^2+28*l^2,?_⟩; rw [hl] at ma; linear_combination ma
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<7)
      (by simpa using Int.natAbs_dvd_natAbs.mpr (ip.dvd_of_dvd_pow pa))
      (by simpa using Int.natAbs_dvd_natAbs.mpr hb)) cop
  have rn : r≠0 := by intro h; rw [h] at sr; linarith
  have vn : v≠0 := by intro h; rw [h] at sa; linarith
  have wn : w≠0 := by intro h; rw [h] at sb; linarith
  have es : IsSquare (((M^2+28776*b^4:ℤ):ℚ)) := by
    refine ⟨49*(b:ℚ)^2*y/(r*v*w),?_⟩
    rw [←sq, div_pow]
    apply (eq_div_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero rn vn) wn))).mpr
    have h : (r*v*w)^2=7*(s*(s-4)*(16*s-15)) := by rw [mul_pow,mul_pow,←sr,←sa,←sb]; ring
    dsimp [M]; push_cast; rw [←sl,h]
    linear_combination -2401*(b:ℚ)^4*curve
  obtain ⟨Z0,hZ⟩:=Rat.isSquare_intCast_iff.mp es
  let Z:=|Z0|
  have ze : Z^2=M^2+28776*b^4 := by simpa [Z,sq_abs,pow_two] using hZ.symm
  have gt : |M|<Z := by
    have pos:=pow_pos bp 4
    have zpos : 0≤Z:=abs_nonneg _
    have ms : |M|^2=M^2:=sq_abs M
    nlinarith only [ze,pos,zpos,ms,abs_nonneg M]
  have parity : (2:ℤ) ∣ Z-M := by
    have zz := congrArg (Int.castRingHom (ZMod 2)) ze
    have equal : (Z:ZMod 2)=(M:ZMod 2) := by
      change (Z^2:ℤ)=(M^2+28776*b^4:ℤ) at ze
      have zz' : (Z:ZMod 2)^2=(M:ZMod 2)^2 := by
        have zero : (28776 : ZMod 2)=0 := by decide
        simpa [zero] using zz
      exact (show ∀ x y:ZMod 2,x^2=y^2 → x=y by decide) _ _ zz'
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [equal]; ring)
  obtain ⟨P,hP⟩:=parity
  refine ⟨⟨a,b,P,M+P,A,B,cop,bp,odd7,sl,hA,hB,?_,?_,by ring,?_⟩⟩
  · linarith only [hP,gt,le_abs_self M]
  · linarith only [hP,gt,neg_abs_le M]
  · have zz : Z=2*P+M:=by linarith only [hP]
    rw [zz] at ze; change P*(M+P)=7194*b^4; nlinarith only [ze]

end Sun28.ConicSelection
#print axioms Sun28.ConicSelection.physical_factors