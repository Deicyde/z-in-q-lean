import MarkedAlternative
import PartnerSmallPlaces
import OddGlobal

namespace Sun28.Abscissa
open Sun28.SelmerRealization Sun28.SeededPartners Sun28.NormPartners Sun28.GlobalSections
open Sun28.PairedClasses ZInQ.RouteK
noncomputable section

/-- For a positive proper squarefree factor b of l, the remaining descent coordinate
is a positive divisor of l. The first coordinate is fixed by that divisor. -/
structure DivisorLabel (b l m : ℕ) : Prop where
  positive : 0 < m
  divides : m∣l
  mod_three : m%3=1
  rational : Cover ℚ l (sqf ((b:ℚ)*m)) m

theorem divisor_of_strict_coordinates {b l : ℕ} (bp : 0 < b) (res : l%12=11)
    {u y : ℚ} (un : u≠0) (yn : y≠0)
    (eq : y^2=((b:ℚ)*u^2)*(b*u^2-l)*(b*u^2+3*l)) :
    ∃ m, DivisorLabel b l m ∧ (sqf ((b:ℚ)*u^2-l))=m := by
  let x:ℚ := b*u^2
  have xp : 0 < x := mul_pos (by exact_mod_cast bp) (sq_pos_of_ne_zero un)
  have lp : 0 < l := by omega
  have ls : 0 < (l:ℚ) := by exact_mod_cast lp
  change y^2=x*(x-l)*(x+3*l) at eq
  have plus : 0 < x+3*l := by positivity
  have minus : 0 < x-l := by
    have pos := eq ▸ sq_pos_of_ne_zero yn
    exact pos_of_mul_pos_right (pos_of_mul_pos_left pos plus.le) xp.le
  let i:=sqf (x-(l:ℚ))
  have ip : 0 < i := (sqf_pos_iff minus.ne').mpr minus
  let m:=i.natAbs
  have cast : (m:ℤ)=i := Int.natAbs_of_nonneg ip.le
  have mp : 0 < m := Int.natAbs_pos.mpr ip.ne'
  obtain ⟨si,v,vn,V⟩:=sqf_spec minus.ne'
  change x-l=(i:ℚ)*v^2 at V
  have V' : x-l=(m:ℚ)*v^2 := by exact_mod_cast (show x-l=((m:ℤ):ℚ)*v^2 by rw [cast]; exact V)
  have mm:(m:ℚ)≠0 := by exact_mod_cast mp.ne'
  have bb:(b:ℚ)≠0 := by exact_mod_cast bp.ne'
  let z:=y/((b:ℚ)*u*m*v)
  have zn:z≠0 := div_ne_zero yn (mul_ne_zero (mul_ne_zero (mul_ne_zero bb un) mm) vn)
  have A : x+3*l=((b:ℚ)*m)*z^2 := by
    dsimp [z]; field_simp
    rw [V'] at eq
    dsimp [x] at eq ⊢
    linear_combination -eq
  let a:=sqf ((b:ℚ)*m)
  obtain ⟨sa,t,tn,T⟩:=sqf_spec (mul_ne_zero bb mm)
  change (b:ℚ)*m=(a:ℚ)*t^2 at T
  have cover : Cover ℚ l a m := by
    refine ⟨t*u/m,v,t*z,1,Or.inr (Or.inr (Or.inr one_ne_zero)),?_,?_⟩
    · push_cast; field_simp
      dsimp [x] at V';linear_combination m*V' - u^2*T
    · push_cast; field_simp
      dsimp [x] at A
      linear_combination -m*A + (u^2-m*z^2)*T
  have sm : Squarefree (m:ℤ) := cast ▸ si
  have loc : (a,(m:ℤ))∈localClasses l := ⟨sa,sm,cover_map cover,fun p _=>cover_map cover⟩
  have dv := (Sun28.MarkedOdd.local_support_dvd lp.ne' loc).2
  have small := small_places res loc
  have three : m%3=1 := by omega
  have two : m%2=1 := by omega
  have cop : m.Coprime 6 := by
    change m.Coprime (2*3)
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm.mul_right
      (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)).symm
  have D : m∣6*l := by exact_mod_cast dv
  exact ⟨m,⟨mp,cop.dvd_of_dvd_mul_left D,three,cover⟩,cast.symm⟩

private theorem not_square {m:ℕ} (s : Squarefree m) (h : 1 < m) : ¬IsSquare (m:ℚ) := by
  rintro sq
  obtain ⟨k,e⟩:=Rat.isSquare_natCast_iff.mp sq
  rw [e] at s h
  have unit := s k dvd_rfl
  rw [Nat.isUnit_iff] at unit
  simp [unit] at h

theorem strict_of_divisor {b k l m : ℕ} (hb:1 < b) (hk:1 < k) (L:l=b*k)
    (sf:Squarefree l) (D:DivisorLabel b l m) : strictPoint b l := by
  let a:=sqf ((b:ℚ)*m)
  have bb:0 < (b:ℚ):=by exact_mod_cast (show 0 < b by omega)
  have kk:0 < (k:ℚ):=by exact_mod_cast (show 0 < k by omega)
  have mm:0 < (m:ℚ):=by exact_mod_cast D.positive
  obtain ⟨_,t,tn,T⟩:=sqf_spec (mul_pos bb mm).ne'
  change (b:ℚ)*m=(a:ℚ)*t^2 at T
  have ap:0 < (a:ℚ):=pos_of_mul_pos_left (T ▸ mul_pos bb mm) (sq_nonneg t)
  obtain ⟨X,Y,Z,W,live,E,F⟩:=D.rational
  change (a:ℚ)*m*X^2-(m:ℚ)*Y^2=(l:ℚ)*W^2 at E
  change (a:ℚ)*Z^2-(a:ℚ)*m*X^2=3*(l:ℚ)*W^2 at F
  have LQ:(l:ℚ)=(b:ℚ)*k:=by exact_mod_cast L
  have ll:0 < (l:ℚ):=LQ ▸ mul_pos bb kk
  obtain ⟨_,sb,sk⟩:=Nat.squarefree_mul_iff.mp (L ▸ sf)
  have Wn : W≠0 := by
    rintro rfl
    by_cases Xn:X=0
    · subst X
      simp only [zero_pow (by decide : 2≠0),mul_zero,zero_sub,neg_eq_zero,mul_eq_zero,pow_eq_zero_iff,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] at E F
      simp_all [mm.ne',ap.ne']
    · have AY : (a:ℚ)*X^2=Y^2 := by apply mul_left_cancel₀ mm.ne';linear_combination E
      have MZ : (m:ℚ)*X^2=Z^2 := by apply mul_left_cancel₀ ap.ne';linear_combination -F
      have nz : Z≠0 := by rintro rfl;exact (mul_ne_zero mm.ne' (pow_ne_zero 2 Xn)) (by simpa using MZ)
      apply not_square sb hb
      refine ⟨Y*t/Z,?_⟩
      field_simp
      linear_combination X^2*T + t^2*AY - (b:ℚ)*MZ
  let u:=(m:ℚ)/t*X/W
  have H : (b:ℚ)*u^2=(a:ℚ)*m*(X/W)^2 := by dsimp [u];field_simp;linear_combination X^2*T
  let z:=(Z/W)
  have V : (b:ℚ)*u^2-l=(m:ℚ)*(Y/W)^2 := by rw [H];field_simp;linear_combination E
  have Z' : (b:ℚ)*u^2+3*l=(a:ℚ)*z^2 := by rw [H];dsimp [z];field_simp;linear_combination -F
  have un : u≠0 := by rintro zero;rw [zero] at V;nlinarith [sq_nonneg (Y/W)]
  have yn : Y/W≠0 := by
    intro zY
    rw [zY] at V
    apply not_square sk hk
    refine ⟨u,?_⟩
    apply mul_left_cancel₀ bb.ne'
    rw [LQ] at V
    linear_combination -V
  have zn : z≠0 := by rintro zero;rw [zero] at Z';nlinarith [mul_nonneg bb.le (sq_nonneg u)]
  let y:=(a:ℚ)*m*(X/W)*(Y/W)*z
  have xn:X/W≠0 := fun h=>un (by dsimp [u];rw [mul_div_assoc,h,mul_zero])
  refine ⟨u,y,un,mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ap.ne' mm.ne') xn) yn) zn,?_⟩
  rw [V,Z',H];dsimp [y];ring

theorem strict_iff_divisor {b k l : ℕ} (hb:1 < b) (hk:1 < k) (L:l=b*k)
    (sf:Squarefree l) (res:l%12=11) : strictPoint b l ↔ ∃ m, DivisorLabel b l m := by
  constructor
  · rintro ⟨u,y,un,yn,h⟩
    obtain ⟨m,D,_⟩:=divisor_of_strict_coordinates (by omega) res un yn h
    exact ⟨m,D⟩
  · rintro ⟨m,D⟩
    exact strict_of_divisor hb hk L sf D

end
end Sun28.Abscissa
#print axioms Sun28.Abscissa.divisor_of_strict_coordinates
#print axioms Sun28.Abscissa.strict_of_divisor
#print axioms Sun28.Abscissa.strict_iff_divisor
