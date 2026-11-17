import TwistParameter
import PoleRescaling

namespace Sun28.TwistExtension
open PreparedPoles PairedClasses Ordinary
noncomputable section

/-- A nonzero abscissa in the required class on a rational twist. -/
def Point (b l : ℚ) : Prop := ∃ t y : ℚ, t≠0 ∧
  y^2=(b*t^2)*(b*t^2-l)*(b*t^2+3*l)

private theorem param_scale (a b s t : ℚ) (hd : s^2+3*b ≠ 0)
    (h : a*(s^2+3*b)=b*(s^2-b)) :
    a*t^2 = b*quartic b s 1*(t/(s^2+3*b))^2 := by
  simp only [quartic,one_pow,mul_one]
  rw [←mul_assoc,←h,div_pow]
  field_simp

theorem point_quartic {β l : ℚ} (hp : 0 < β) (ln : l≠0) :
    Point β l ↔ ∃ u v w : ℚ, (l:ℚ) = β * quartic β u v * w^2 := by
  constructor
  · rintro ⟨t,y,ht,hy⟩
    by_cases tors : (β:ℚ)*t^2 = l
    · exact ⟨1,0,t,by simpa [quartic] using tors.symm⟩
    let a : ℚ := l/t^2
    let Y : ℚ := y/t^3
    have eqL : a*t^2 = l := by dsimp [a]; field_simp
    have eqY : Y*t^3 = y := by dsimp [Y]; field_simp
    have scaled : Y^2 = (β:ℚ)*(β-a)*(β+3*a) := by
      have eq : (Y^2 - β*(β-a)*(β+3*a))*t^6=0 := by
        rw [←eqY,←eqL] at hy
        linear_combination hy
      exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right (pow_ne_zero 6 ht))
    have sub : (β:ℚ)-a ≠ 0 := by
      intro h
      exact tors ((sub_eq_zero.mp h) ▸ eqL)
    let s := Y/((β:ℚ)-a)
    have line : s*((β:ℚ)-a)=Y := by dsimp [s]; field_simp
    have se : s^2*((β:ℚ)-a) = β*(β+3*a) := by
      apply mul_right_cancel₀ sub
      rw [←line] at scaled
      linear_combination scaled
    have D : 0 < s^2+3*(β:ℚ) := by positivity
    refine ⟨s,1,t/(s^2+3*β),?_⟩
    exact eqL.symm.trans (param_scale a β s t D.ne' (by linear_combination -se))
  · rintro ⟨u,v,w,e⟩
    let D := u^2+3*(β:ℚ)*v^2
    have hD : D ≠ 0 := by
      rintro zero
      have le : (l:ℚ)=0 := by
        change (l:ℚ) = β*((u^2-β*v^2)*D)*w^2 at e
        rw [zero] at e
        simpa only [mul_zero,zero_mul] using e
      exact ln le
    have hw : w ≠ 0 := by rintro rfl; simp at e; exact ln e
    refine ⟨D*w,4*(β:ℚ)^2*u*v*D^2*w^3,mul_ne_zero hD hw,?_⟩
    rw [e]
    dsimp [D,quartic]
    ring

/-- Two binary quartic values with a nonzero product. -/
def Surface (b θ : ℚ) : Prop := ∃ u v U V W : ℚ, W≠0 ∧
  W^2=θ*quartic b u v*quartic b U V

theorem surface_iff_pair {b θ : ℚ} (bp : 0<b) (tp : θ≠0) :
    Surface b θ ↔ ∃ l : ℚ, l≠0 ∧ Point b l ∧ Point b (l*θ) := by
  constructor
  · rintro ⟨u,v,U,V,W,wn,e⟩
    have prod : θ*quartic b u v*quartic b U V≠0 := e ▸ pow_ne_zero 2 wn
    have f:=right_ne_zero_of_mul (left_ne_zero_of_mul prod)
    have g:=right_ne_zero_of_mul prod
    let l:=b*quartic b u v
    have ln : l≠0:=mul_ne_zero bp.ne' f
    refine ⟨l,ln,(point_quartic bp ln).mpr ⟨u,v,1,by dsimp [l];ring⟩,
      (point_quartic bp (mul_ne_zero ln tp)).mpr ⟨U,V,W/quartic b U V,?_⟩⟩
    dsimp [l];field_simp;linear_combination -e
  · rintro ⟨l,ln,one,two⟩
    obtain ⟨u,v,w,a⟩:=(point_quartic bp ln).mp one
    obtain ⟨U,V,z,c⟩:=(point_quartic bp (mul_ne_zero ln tp)).mp two
    have wn : w≠0:=by rintro rfl; simp at a;exact ln a
    have zn : z≠0:=by rintro rfl; simp at c; rcases c with h|h <;> contradiction
    have gn : quartic b U V≠0 := by
      intro h
      exact (mul_ne_zero ln tp) (by simpa [h] using c)
    refine ⟨u,v,U,V,quartic b U V*z/w,div_ne_zero (mul_ne_zero gn zn) wn,?_⟩
    rw [div_pow,div_eq_iff (pow_ne_zero 2 wn)]
    rw [a] at c
    apply mul_left_cancel₀ bp.ne'
    linear_combination -(quartic b U V)*c

theorem branch_iff_surface {μ B b θ a d : ℚ} (bp : 0<b) (tn : θ≠0) (an : a≠0) (dn : d≠0)
    (A : μ*B=b*a^2) (H : (μ*B)*(μ*B-B^2)=θ*d^2) :
    (∃ e z : ℚ,poleBranch μ B e z) ↔ Surface b θ := by
  rw [surface_iff_pair bp tn]
  constructor
  · rintro ⟨e,z,guard,Y,Z,first,second⟩
    obtain ⟨g,zn⟩:=mul_ne_zero_iff.mp guard
    have en:=right_ne_zero_of_mul (left_ne_zero_of_mul g)
    refine ⟨e,en,⟨a,Y,an,by simpa only [←A] using first⟩,
      ⟨a*z/d,z*Z/d^3,div_ne_zero (mul_ne_zero an zn) dn,?_⟩⟩
    change Z^2=(μ*B)*(μ*B*z^2-e*((μ*B)*(μ*B-B^2)))*(μ*B*z^2+3*e*((μ*B)*(μ*B-B^2))) at second
    rw [H,A] at second
    field_simp
    linear_combination second
  · rintro ⟨l,ln,⟨u,y,un,ey⟩,⟨v,w,vn,ew⟩⟩
    let t:=a/u
    let z:=d*v/u
    have nz:=div_ne_zero (mul_ne_zero dn vn) un
    have hA : μ*B≠0 := A ▸ mul_ne_zero bp.ne' (pow_ne_zero 2 an)
    have hH : (μ*B)*(μ*B-B^2)≠0:=H ▸ mul_ne_zero tn (pow_ne_zero 2 dn)
    refine ⟨l*t^2,z,mul_ne_zero (mul_ne_zero (mul_ne_zero hA
      (mul_ne_zero ln (pow_ne_zero _ (div_ne_zero an un)))) hH) nz,y*t^3,w*(t*d)^3/z,?_,?_⟩
    · dsimp only [t];rw [A];field_simp;linear_combination ey
    · rw [H,A];dsimp only [t,z];field_simp;linear_combination ew

end
end Sun28.TwistExtension
#print axioms Sun28.TwistExtension.point_quartic
#print axioms Sun28.TwistExtension.surface_iff_pair
#print axioms Sun28.TwistExtension.branch_iff_surface
