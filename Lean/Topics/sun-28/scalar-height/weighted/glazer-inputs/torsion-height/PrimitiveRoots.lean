import OrderTests
import Mathlib.Data.ZMod.Basic

namespace ZInQBlueprint.MarkedTorsion
section
variable {R S:Type*} [CommRing R] [CommRing S]

def weight : Test → ℕ
  | .atStart => 3 | .atDouble => 12 | .atFour => 48 | .threeAfterDouble => 16

private theorem f_scale (a b c k u v:R) : F a b c (k*u) (k*v) = k^3*F a b c u v := by unfold F;ring
private theorem n_scale (a b c k u v:R) : N a b c (k*u) (k*v) = k^4*N a b c u v := by unfold N;ring
private theorem d_scale (a b c k u v:R) : D a b c (k*u) (k*v) = k^4*D a b c u v := by unfold D;rw [f_scale];ring
private theorem psi_scale (a b c k u v:R) : Psi a b c (k*u) (k*v) = k^4*Psi a b c u v := by unfold Psi;ring

theorem test_scale (a b c k u v:R) (j:Test) :
    test a b c j (k*u) (k*v) = k^weight j * test a b c j u v := by
  cases j <;> simp only [test,dup,weight,n_scale,d_scale,psi_scale,f_scale,←pow_mul]

theorem map_test (g:R →+* S) (a b c u v:R) (j:Test) :
    g (test a b c j u v)=test (g a) (g b) (g c) j (g u) (g v) := by
  cases j <;> simp [test,dup,N,D,F,Psi,map_ofNat]

def top : Test → ℤ
  | .threeAfterDouble => 3 | _ => 1

theorem test_at_infty (a b c:R) (j:Test) : test a b c j 1 0=(top j:R) := by
  cases j <;> simp [top,test,dup,F,N,D,Psi]

end

theorem primitive_root {a b c u v : ℤ} (prim:Nat.Coprime u.natAbs v.natAbs)
    (j:Test) (h:test a b c j (u+3*v) v=0) :
    u.natAbs ∣ (test a b c j 3 1).natAbs ∧ v.natAbs ∣ (top j).natAbs := by
  constructor
  · let g:=Int.castRingHom (ZMod u.natAbs)
    have uz : g u=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (by simp)
    have z:=congrArg g h
    rw [map_test,map_zero,map_add,map_mul,uz,zero_add,map_ofNat] at z
    have zz:=test_scale (g a) (g b) (g c) (g v) (3:ZMod u.natAbs) 1 j
    rw [mul_one,mul_comm (g v) 3] at zz
    rw [zz] at z
    have mt:=map_test g a b c 3 1 j
    simp only [map_ofNat,map_one] at mt
    rw [←mt] at z
    have ee : g (v^weight j * test a b c j 3 1)=0 := by simpa only [map_mul,map_pow] using z
    have dv:=Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp ee)
    simp only [Int.natAbs_natCast,Int.natAbs_mul,Int.natAbs_pow] at dv
    exact (prim.pow_right _).dvd_of_dvd_mul_left dv
  · let g:=Int.castRingHom (ZMod v.natAbs)
    have vz : g v=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (by simp)
    have z:=congrArg g h
    rw [map_test,map_zero,map_add,map_mul,vz,mul_zero,add_zero] at z
    have zz:=test_scale (g a) (g b) (g c) (g u) 1 0 j
    rw [mul_one,mul_zero,test_at_infty] at zz
    rw [zz] at z
    have ee : g (u^weight j * top j)=0 := by rw [map_mul,map_pow];exact z
    have dv:=Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp ee)
    simp only [Int.natAbs_natCast,Int.natAbs_mul,Int.natAbs_pow] at dv
    exact (prim.symm.pow_right _).dvd_of_dvd_mul_left dv

theorem rational_root {a b c:ℤ} (z:ℚ) (j:Test) (h:test (a:ℚ) b c j (z+3) 1=0) :
    z.num.natAbs ∣ (test a b c j 3 1).natAbs ∧ z.den ∣ (top j).natAbs := by
  apply primitive_root (v:=(z.den:ℤ)) (by simpa using z.reduced) j
  apply Int.cast_injective (α:=ℚ)
  let g:=Int.castRingHom ℚ
  change g _ = g 0
  rw [map_test,map_add,map_mul,map_ofNat,map_zero]
  have dn : g (z.den:ℤ) = (z.den:ℚ) := by simp [g]
  rw [dn]
  have eq : (z.den:ℚ)*(z+3)=g z.num+3*z.den := by
    have hz:=z.num_div_den; dsimp [g];field_simp at hz;linear_combination -hz
  have t:=test_scale (g a) (g b) (g c) (z.den:ℚ) (z+3) 1 j
  change test (g a) (g b) (g c) j (z+3) 1=0 at h
  rw [eq,mul_one,h,mul_zero] at t
  exact t

end ZInQBlueprint.MarkedTorsion
#print axioms ZInQBlueprint.MarkedTorsion.primitive_root
#print axioms ZInQBlueprint.MarkedTorsion.rational_root
