import BezoutData
import Mathlib.RingTheory.Coprime.Lemmas

namespace ZInQBlueprint.MarkedTorsion
set_option exponentiation.threshold 1024

def box (u v:ℤ) : ℤ := max |u| |v|

theorem primitive_proportional {n e u v:ℤ} (primitive:IsCoprime u v)
    (eq:n*v=e*u) : ∃ g:ℤ,n=g*u ∧ e=g*v := by
  obtain ⟨s,t,one⟩:=primitive
  refine ⟨s*n+t*e,?_,?_⟩
  · linear_combination -n*one+t*eq
  · linear_combination -e*one-s*eq

private theorem poly3_bound (co:Fin 4→ℤ) (u v:ℤ) :
    |poly3 co u v| ≤ polyNorm co*(box u v)^3 := by
  let H:=box u v
  have hu:|u|≤H:=le_max_left ..
  have hv:|v|≤H:=le_max_right ..
  have Hn:0≤H:=(abs_nonneg u).trans hu
  calc
    |poly3 co u v| ≤ |co 0| * |v|^3+ |co 1| * |u| * |v|^2+ |co 2| * |u|^2* |v| + |co 3| * |u|^3 := by
      unfold poly3
      calc
        _ ≤ |co 0*v^3+co 1*u*v^2+co 2*u^2*v| + |co 3*u^3| := abs_add_le .. 
        _ ≤ (|co 0*v^3+co 1*u*v^2| + |co 2*u^2*v|)+ |co 3*u^3| := by gcongr;apply abs_add_le
        _ ≤ (|co 0*v^3| + |co 1*u*v^2| + |co 2*u^2*v|)+ |co 3*u^3| := by gcongr;apply abs_add_le
        _ = _ := by simp only [abs_mul,abs_pow]
    _ ≤ |co 0| * H^3+ |co 1| * H*H^2+ |co 2| * H^2*H+ |co 3| * H^3 := by gcongr
    _ = _ := by unfold polyNorm;change _=_*H^3;ring

theorem primitive_growth (j:Fin 5) {u v n e g:ℤ} (prim:IsCoprime u v)
    (nrep:N (a j) (b j) (c j) u v=g*n)
    (erep:D (a j) (b j) (c j) u v=g*e) (hp:0<box u v) :
    (box u v)^4 ≤ 2^180*box n e := by
  obtain ⟨rpos,cap0,cap1⟩:=cofactor_bounds j
  obtain ⟨x,y⟩:=bezout_relations j u v
  rw [nrep,erep] at x y
  have du:g∣bezoutR j*u^7 := ⟨_,x.symm.trans (by ring : _=g*(poly3 (cof j 0) u v*n+poly3 (cof j 1) u v*e))⟩
  have dv:g∣bezoutR j*v^7 := ⟨_,y.symm.trans (by ring : _=g*(poly3 (cof j 2) u v*n+poly3 (cof j 3) u v*e))⟩
  obtain ⟨z,t,one⟩:=prim.pow (m:=7) (n:=7)
  have gcd:g∣bezoutR j := by
    have d:=dvd_add (du.mul_left z) (dv.mul_left t)
    convert d using 1; linear_combination -(bezoutR j)*one
  have gb:|g|≤bezoutR j := by
    have q:=Nat.le_of_dvd (Int.natAbs_pos.mpr rpos.ne') (Int.natAbs_dvd_natAbs.mpr gcd)
    have h:=Int.ofNat_le.mpr q
    simpa only [Int.natCast_natAbs,abs_of_pos rpos] using h
  let H:=box u v
  have h0:0≤H:=hp.le
  let HH:=box n e
  have hh:0≤HH:=(abs_nonneg n).trans (le_max_left ..)
  have endbound (i l:Fin 4) (w:ℤ) (cap:polyNorm (cof j i)+polyNorm (cof j l)≤2^180)
      (id:poly3 (cof j i) u v*(g*n)+poly3 (cof j l) u v*(g*e)=bezoutR j*w^7) :
      bezoutR j* |w|^7 ≤ bezoutR j*(2^180*HH)*H^3 := by
    have q0:=poly3_bound (cof j i) u v
    have q1:=poly3_bound (cof j l) u v
    have nn : |n|≤HH:=le_max_left ..
    have ee : |e|≤HH:=le_max_right ..
    have normN (i:Fin 4) : 0≤polyNorm (cof j i) := by unfold polyNorm;positivity
    have ni:=normN i
    have nl:=normN l
    calc
      _ = |bezoutR j*w^7|:=by rw [abs_mul,abs_pow,abs_of_pos rpos]
      _ ≤ |poly3 (cof j i) u v| * |g| * |n| + |poly3 (cof j l) u v| * |g| * |e| := by
        rw [←id];simpa only [abs_mul,mul_assoc] using abs_add_le (poly3 (cof j i) u v*(g*n)) (poly3 (cof j l) u v*(g*e))
      _ ≤ (polyNorm (cof j i)*H^3)*bezoutR j*HH+(polyNorm (cof j l)*H^3)*bezoutR j*HH := by
        gcongr
      _ = bezoutR j*((polyNorm (cof j i)+polyNorm (cof j l))*HH)*H^3:=by ring
      _ ≤ _ := by gcongr
  have lim : bezoutR j*H^7 ≤ bezoutR j*(2^180*HH)*H^3 := by
    rcases le_total |u| |v| with q|q
    · simpa only [H,box,max_eq_right q] using endbound 2 3 v cap1 y
    · simpa only [H,box,max_eq_left q] using endbound 0 1 u cap0 x
  rw [mul_assoc] at lim
  have ll: H^7≤(2^180*HH)*H^3 := (mul_le_mul_iff_right₀ rpos).mp lim
  rw [show H^7=H^4*H^3 by ring] at ll
  exact (mul_le_mul_iff_left₀ (pow_pos hp 3)).mp ll

end ZInQBlueprint.MarkedTorsion
#print axioms ZInQBlueprint.MarkedTorsion.primitive_proportional
#print axioms ZInQBlueprint.MarkedTorsion.primitive_growth
