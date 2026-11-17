import RatioChart
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Sun28.PointLifts
noncomputable section

/-- A rational residue represented by an integer fraction with denominator prime to p. -/
def Residue (p : ℕ) (z : ℚ) (r : ZMod p) : Prop :=
  ∃ n d : ℤ, (d:ZMod p)≠0 ∧ z=(n:ℚ)/d ∧ (n:ZMod p)=r*d

private theorem int_ne {p : ℕ} {d : ℤ} (h : (d:ZMod p)≠0) : (d:ℚ)≠0 := by
  intro e;apply h;have a : d=0:=by exact_mod_cast e
  simp [a]

theorem residue_int {p : ℕ} [Fact p.Prime] (n : ℤ) : Residue p (n:ℚ) n :=
  ⟨n,1,by simp,by simp,by simp⟩

theorem residue_unique {p : ℕ} [Fact p.Prime] {z : ℚ} {r s : ZMod p}
    (h : Residue p z r) (k : Residue p z s) : r=s := by
  obtain ⟨a,b,bn,e,f⟩:=h
  obtain ⟨c,d,dn,g,j⟩:=k
  have Q:= (div_eq_div_iff (int_ne bn) (int_ne dn)).mp (e.symm.trans g)
  have eq : a*d=c*b:=by exact_mod_cast Q
  have modEq : (a:ZMod p)*d=c*b:=by exact_mod_cast congrArg (Int.castRingHom (ZMod p)) eq
  rw [f,j] at modEq
  apply mul_right_cancel₀ (mul_ne_zero bn dn)
  linear_combination modEq

theorem residue_mul {p : ℕ} [Fact p.Prime] {z w : ℚ} {r s : ZMod p}
    (h : Residue p z r) (k : Residue p w s) : Residue p (z*w) (r*s) := by
  obtain ⟨a,b,bn,e,f⟩:=h
  obtain ⟨c,d,dn,g,j⟩:=k
  refine ⟨a*c,b*d,by simpa using mul_ne_zero bn dn,?_,?_⟩
  · rw [e,g];push_cast;ring
  · push_cast;rw [f,j];ring

theorem residue_div {p : ℕ} [Fact p.Prime] {z w : ℚ} {r s : ZMod p}
    (h : Residue p z r) (k : Residue p w s) (sn : s≠0) : Residue p (z/w) (r/s) := by
  obtain ⟨a,b,bn,e,f⟩:=h
  obtain ⟨c,d,dn,g,j⟩:=k
  have cn : (c:ZMod p)≠0:=j ▸ mul_ne_zero sn dn
  refine ⟨a*d,b*c,by simpa using mul_ne_zero bn cn,?_,?_⟩
  · rw [e,g];push_cast;simp only [div_eq_mul_inv,mul_inv_rev,inv_inv];ring
  · push_cast;rw [f,j];field_simp

theorem order_zero_of_residue {p : ℕ} [Fact p.Prime] {z : ℚ} {r : ZMod p}
    (h : Residue p z r) (rn : r≠0) : padicValRat p z=0 := by
  obtain ⟨a,b,bn,e,f⟩:=h
  have an : (a:ZMod p)≠0:=f ▸ mul_ne_zero rn bn
  rw [e,padicValRat.div (int_ne an) (int_ne bn),padicValRat.of_int,padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd (mt (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr an),
    padicValInt.eq_zero_of_not_dvd (mt (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr bn)]
  simp

private theorem abscissa_scale (b t k : ℚ) (kn : k≠0) :
    abscissa b (t*k) k=abscissa b t 1 := by
  unfold abscissa
  rw [show (t*k)^2+3*b*k^2=(t^2+3*b)*k^2 by ring,
    show (t*k)^2-b*k^2=(t^2-b)*k^2 by ring]
  simpa only [one_pow,mul_one] using (mul_div_mul_right (t^2+3*b) (t^2-b) (pow_ne_zero 2 kn))

/-- A primitive integral parameter for every point of the conic, including its two horizontal endpoints. -/
theorem integral_abscissa {b : ℕ} {z h : ℚ} (bp : 0<b)
    (E : (z-1)*(z+3)=(b:ℚ)*h^2) :
    ∃ x y : ℤ, x.natAbs.Coprime y.natAbs ∧ z=abscissa b x y := by
  obtain ⟨u,v,uv,_,ze⟩:=conic_parameter (by exact_mod_cast bp.ne') E
  by_cases vn : v=0
  · subst v
    have un : u≠0:=uv.resolve_right (by simp)
    exact ⟨1,0,by simp,by simpa [abscissa,un] using ze⟩
  · let t:=u/v
    have ux : t*v=u:=div_mul_cancel₀ _ vn
    have dp : (t.den:ℚ)≠0:=by exact_mod_cast t.den_nz
    have nx : t*t.den=t.num:=(eq_div_iff dp).mp (Rat.num_div_den t).symm
    refine ⟨t.num,(t.den:ℤ),by simpa using t.reduced,?_⟩
    rw [ze,←ux,abscissa_scale _ _ _ vn]
    push_cast
    rw [←nx,abscissa_scale _ _ _ dp]

theorem primitive_mod {p : ℕ} [h : Fact p.Prime] {x y : ℤ}
    (cop : x.natAbs.Coprime y.natAbs) : (x:ZMod p)≠0 ∨ (y:ZMod p)≠0 := by
  by_contra! both
  have i:=(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp both.1
  have j:=(ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp both.2
  have I:=Int.natAbs_dvd_natAbs.mpr i
  have J:=Int.natAbs_dvd_natAbs.mpr j
  exact Nat.not_coprime_of_dvd_of_dvd h.out.one_lt (by simpa using I) (by simpa using J) cop

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.residue_unique
#print axioms Sun28.PointLifts.order_zero_of_residue
#print axioms Sun28.PointLifts.integral_abscissa
