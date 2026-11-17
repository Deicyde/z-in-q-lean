import OddImages
import ZInQKernel.RouteK.Selmer.Bits

namespace Sun28.MarkedOdd
open Sun28.SelmerRealization ZInQ.RouteK ZInQ.RouteK.Selmer
variable {p : ℕ} [hp : Fact p.Prime]

private theorem unit_bit {u : ℤ} (p2 : p≠2) (uu : ¬(p:ℤ)∣u) (h : IsSquare (u:Qp p)) :
    legBit p u = 0 := by
  have norm : ‖(u:ℤ_[p])‖=1 := by rw [PadicInt.norm_def,PadicInt.coe_intCast];exact padic_norm_intCast_eq_one uu
  have iff := isSquare_coe_iff_toZMod p2 norm
  rw [PadicInt.coe_intCast,map_intCast] at iff
  simp [legBit,iff.mp h]

private theorem zero_cast {u : ℤ} (h : ¬(p:ℤ)∣u) : (u:ZMod p) ≠ 0 := by
  rwa [ne_eq,ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Prime-power and unit conditions on both marked labels. The exponents are
the prescribed decomposition bits; the two Legendre-symbol rows are in F₂. -/
theorem bad_rows_of_decomposition (p2 : p≠2) (p3 : p≠3) {l : ℕ} (pl : p ∣ l)
    (sl : Squarefree l) {a b U V m : ℤ} {x y : ℕ} (hx : x<2) (hy : y<2)
    (A : a=(p:ℤ)^x*U) (B : b=(p:ℤ)^y*V) (L : (l:ℤ)=(p:ℤ)*m)
    (un : ¬ (p:ℤ)∣U) (vn : ¬ (p:ℤ)∣V) (mn : ¬ (p:ℤ)∣m) (cover : Cover (Qp p) l a b) :
    legBit p U = (x:ZMod 2)*legBit p m + (y:ZMod 2)*legBit p 3 ∧
    legBit p V = (y:ZMod 2)*legBit p (-m) := by
  have pn : (p:ℤ)≠0 := by exact_mod_cast hp.out.ne_zero
  have nz {w : ℤ} (h : ¬(p:ℤ)∣w) : w≠0 := fun e => h (e ▸ dvd_zero _)
  have an : a≠0 := A ▸ mul_ne_zero (pow_ne_zero _ pn) (nz un)
  have bn : b≠0 := B ▸ mul_ne_zero (pow_ne_zero _ pn) (nz vn)
  obtain ⟨i,j,hi,hj,sa,sb⟩ := bad_basis p2 p3 pl sl an bn cover
  have t : ¬(p:ℤ)∣3 := fun h => p3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp (by exact_mod_cast h))
  have prime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have nmn : ¬(p:ℤ)∣-m := by simpa
  have nzMul {s t : ℤ} (hs : ¬(p:ℤ)∣s) (ht : ¬(p:ℤ)∣t) : ¬(p:ℤ)∣s*t :=
    fun h => (prime.dvd_or_dvd h).elim hs ht
  have nzPow {s : ℤ} (hs : ¬(p:ℤ)∣s) (i : ℕ) : ¬(p:ℤ)∣s^i :=
    fun h => hs (prime.dvd_of_dvd_pow h)
  have u1 := nzMul (nzMul un (nzPow mn i)) (nzPow t j)
  have u2 := nzMul vn (nzPow nmn j)
  have EA : a*(l:ℤ)^i*3^j = (p:ℤ)^(x+i)*(U*m^i*3^j) := by rw [A,L,pow_add,mul_pow];ring
  have EB : b*(-(l:ℤ))^j = (p:ℤ)^(y+j)*(V*(-m)^j) := by
    rw [B,L,show -((p:ℤ)*m)=(p:ℤ)*(-m) by ring,pow_add,mul_pow];ring
  rw [EA,isSquare_padic_pow_mul_iff u1] at sa
  rw [EB,isSquare_padic_pow_mul_iff u2] at sb
  have ix : i=x := by obtain ⟨h,H⟩:=sa.1;omega
  have jy : j=y := by obtain ⟨h,H⟩:=sb.1;omega
  have h1 := unit_bit p2 u1 sa.2
  have h2 := unit_bit p2 u2 sb.2
  have mm := zero_cast mn
  have tt := zero_cast t
  have vm := zero_cast vn
  have nmm := zero_cast nmn
  have uu := zero_cast un
  rw [legBit_mul (zero_cast (nzMul un (nzPow mn i))) (zero_cast (nzPow t j)),
    legBit_mul uu (zero_cast (nzPow mn i)),legBit_pow mm,legBit_pow tt,ix,jy] at h1
  rw [legBit_mul vm (zero_cast (nzPow nmn j)),legBit_pow nmm,jy] at h2
  constructor
  · exact (bits_eq_iff_add_eq_zero _ _).mpr (by rwa [←add_assoc])
  · exact (bits_eq_iff_add_eq_zero _ _).mpr h2

end Sun28.MarkedOdd
#print axioms Sun28.MarkedOdd.bad_rows_of_decomposition
