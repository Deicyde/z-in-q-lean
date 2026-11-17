import BlueprintTwists

namespace Sun28.PairedClasses
open PreparedPoles

/-- The product obtained from the rational conic of scaled abscissas, homogenized
so that the point at infinity includes the rational two-torsion point. -/
def quartic (b u v : ℚ) : ℚ := (u^2 - b*v^2)*(u^2 + 3*b*v^2)

private theorem param_scale (a b s t : ℚ) (hd : s^2+3*b ≠ 0)
    (h : a*(s^2+3*b)=b*(s^2-b)) :
    a*t^2 = b*quartic b s 1*(t/(s^2+3*b))^2 := by
  simp only [quartic,one_pow,mul_one]
  rw [←mul_assoc,←h,div_pow]
  field_simp

theorem twist_iff_quartic {β l : ℕ} (hb : 0 < β) (hl : 0 < l) :
    TwistPoint β l ↔ ∃ u v w : ℚ, (l:ℚ) = β * quartic β u v * w^2 := by
  have hp : 0 < (β:ℚ) := by exact_mod_cast hb
  have lp : 0 < (l:ℚ) := by exact_mod_cast hl
  constructor
  · rintro ⟨t,y,ht,hy⟩
    dsimp at hy
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
      exact lp.ne' le
    have hw : w ≠ 0 := by rintro rfl; simp at e; exact hl.ne' e
    refine ⟨D*w,4*(β:ℚ)^2*u*v*D^2*w^3,mul_ne_zero hD hw,?_⟩
    dsimp
    rw [e]
    dsimp [D,quartic]
    ring

end Sun28.PairedClasses
#print axioms Sun28.PairedClasses.twist_iff_quartic
