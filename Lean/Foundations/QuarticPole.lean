import PoleSurface

/-! Literal pole equations used by the 962-coordinate construction. -/
namespace QuarticPole

def IsSquare (v : Rat) : Prop := ∃ r : Rat, r^2 = v

def Multiplier (A U : Rat) : Rat := A*(A-U^2)

def Block (A V : Rat) : Prop :=
  ∃ e p q s : Rat, p^2 = A*(1-e)*(1+3*e) ∧
    A*q^2 = (s^2-e*V)*(s^2+3*(e*V))

/-- Four witnesses with h evaluated as in the original equations. -/
def LiteralAt (A U : Rat) : Prop :=
  ∃ e p q s : Rat, p^2 = A*(1-e)*(1+3*e) ∧
    let h := e*(A-U^2)
    A*q^2 = (s^2-A*h)*(s^2+3*(A*h))

def Preparation (b t U : Rat) : Prop :=
  (1+b*t^2)*U = b*(1-b*t^2)

def ScalarPole (b : Rat) : Prop :=
  ∃ t U : Rat, Preparation b t U ∧ LiteralAt (17*b) U

def ZeroPole (b : Rat) : Prop := LiteralAt (17*b) b

private theorem cancel {a b s : Rat} (hs : s ≠ 0) (h : a*s=b*s) : a=b := by
  grind

theorem literalAt_iff_block (A U : Rat) :
    LiteralAt A U ↔ Block A (Multiplier A U) := by
  unfold LiteralAt Block
  have h (e : Rat) : A*(e*(A-U^2)) = e*(Multiplier A U) := by
    unfold Multiplier
    grobner
  constructor
  · rintro ⟨e,p,q,s,hp,hq⟩
    exact ⟨e,p,q,s,hp,by simpa only [h] using hq⟩
  · rintro ⟨e,p,q,s,hp,hq⟩
    exact ⟨e,p,q,s,hp,by simpa only [h] using hq⟩

private theorem toGuarded {A V e p q s : Rat} (hA : A ≠ 0)
    (he : e ≠ 0) (hV : V ≠ 0) (hs : s ≠ 0)
    (hp : p^2=A*(1-e)*(1+3*e))
    (hq : A*q^2=(s^2-e*V)*(s^2+3*(e*V))) : PoleSurface.Guarded A V := by
  have hn : (A*e)*V*s ≠ 0 := by grind
  refine ⟨A*e,s,A*p,A^2*q,((A*e)*V*s)⁻¹,Rat.mul_inv_cancel _ hn,?_,?_⟩
  · calc (A*p)^2 = A^2*p^2 := by grobner
         _ = _ := by rw [hp]; grobner
  · calc (A^2*q)^2 = A^3*(A*q^2) := by grobner
         _ = _ := by rw [hq]; grobner

private theorem fromGuarded {A V : Rat} (hA : A ≠ 0)
    (h : PoleSurface.Guarded A V) : Block A V := by
  obtain ⟨E,s,r₁,r₂,_,_,h₁,h₂⟩ := h
  have hA₂ : A^2 ≠ 0 := by grind
  have hA₃ : A^3 ≠ 0 := by grind
  let e := E/A
  let p := r₁/A
  let q := r₂/A^2
  have he : e*A=E := Rat.div_mul_cancel hA
  have hp : p*A=r₁ := Rat.div_mul_cancel hA
  have hq : q*A^2=r₂ := Rat.div_mul_cancel hA₂
  refine ⟨e,p,q,s,?_,?_⟩
  · apply cancel hA₂
    calc p^2*A^2 = (p*A)^2 := by grobner
         _ = _ := by rw [hp,h₁,←he]; grobner
  · apply cancel hA₃
    calc A*q^2*A^3 = (q*A^2)^2 := by grobner
         _ = _ := by rw [hq,h₂,←he]; grobner

private theorem fromSquare {A V : Rat} (h : IsSquare A) : Block A V := by
  obtain ⟨a,ha⟩ := h
  exact ⟨0,a,0,0,by grobner,by grobner⟩

private theorem fromMinusThree {A V : Rat} (hA : A ≠ 0)
    (h : IsSquare (-3*A)) : Block A V := by
  obtain ⟨a,ha⟩ := h
  let q := V*a/A
  have hq : q*A=V*a := Rat.div_mul_cancel hA
  refine ⟨1,0,q,0,by grobner,?_⟩
  apply cancel hA
  calc A*q^2*A = (q*A)^2 := by grobner
       _ = V^2*a^2 := by rw [hq]; grobner
       _ = _ := by rw [ha]; grobner

theorem multiplier_zero_isSquare {A U : Rat} (hA : A ≠ 0)
    (hV : Multiplier A U = 0) : IsSquare A := by
  refine ⟨U,?_⟩
  unfold Multiplier at hV
  grind

private theorem zeroAbscissa {A V e q : Rat} (he : e ≠ 0) (hV : V ≠ 0)
    (h : A*q^2=((0:Rat)^2-e*V)*((0:Rat)^2+3*(e*V))) : IsSquare (-3*A) := by
  have hn : e*V ≠ 0 := by grind
  let y := A*q/(e*V)
  have hy : y*(e*V)=A*q := Rat.div_mul_cancel hn
  refine ⟨y,?_⟩
  apply cancel (s := (e*V)^2) (by grind)
  calc y^2*(e*V)^2 = (y*(e*V))^2 := by grobner
       _ = A*(A*q^2) := by rw [hy]; grobner
       _ = _ := by rw [h]; grobner

/-- Exact unguarded clause, retaining every zero ordinate and degenerate witness. -/
theorem block_iff_projective (A U : Rat) (hA : A ≠ 0) :
    Block A (Multiplier A U) ↔
      IsSquare A ∨ IsSquare (-3*A) ∨ PoleSurface.ProjectiveSurface A (Multiplier A U) := by
  let V := Multiplier A U
  have chart : PoleSurface.Guarded A V ↔ PoleSurface.ProjectiveSurface A V :=
    (PoleSurface.guarded_iff_surface _ _ hA).trans (PoleSurface.surface_iff_projective _ _)
  constructor
  · rintro ⟨e,p,q,s,hp,hq⟩
    by_cases he : e = 0
    · left
      exact ⟨p,by rw [he] at hp; grind⟩
    by_cases hV : V = 0
    · exact Or.inl (multiplier_zero_isSquare hA hV)
    by_cases hs : s = 0
    · subst s
      exact Or.inr (Or.inl (zeroAbscissa he hV hq))
    exact Or.inr (Or.inr (chart.mp (toGuarded hA he hV hs hp hq)))
  · rintro (h | h | h)
    · exact fromSquare h
    · exact fromMinusThree hA h
    · exact fromGuarded hA (chart.mpr h)

theorem literalAt_iff_projective (A U : Rat) (hA : A ≠ 0) :
    LiteralAt A U ↔
      IsSquare A ∨ IsSquare (-3*A) ∨ PoleSurface.ProjectiveSurface A (Multiplier A U) :=
  (literalAt_iff_block A U).trans (block_iff_projective A U hA)

theorem preparation_den_ne_zero {b t U : Rat} (hb : b ≠ 0) (h : Preparation b t U) :
    1+b*t^2 ≠ 0 := by
  unfold Preparation at h
  intro hz
  rw [hz] at h
  grind

/-- The scalar block retains its single rational preparation parameter. -/
theorem scalar_iff_projective (b : Rat) (hb : b ≠ 0) :
    ScalarPole b ↔ IsSquare (17*b) ∨ IsSquare (-3*(17*b)) ∨
      ∃ t U : Rat, Preparation b t U ∧
        PoleSurface.ProjectiveSurface (17*b) (Multiplier (17*b) U) := by
  have hA : 17*b ≠ 0 := by grind
  constructor
  · rintro ⟨t,U,hp,h⟩
    rcases (literalAt_iff_projective _ _ hA).mp h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨t,U,hp,h⟩)
  · rintro (h | h | ⟨t,U,hp,h⟩)
    · exact ⟨0,b,by unfold Preparation; grobner,
        (literalAt_iff_projective _ _ hA).mpr (Or.inl h)⟩
    · exact ⟨0,b,by unfold Preparation; grobner,
        (literalAt_iff_projective _ _ hA).mpr (Or.inr (Or.inl h))⟩
    · exact ⟨t,U,hp,(literalAt_iff_projective _ _ hA).mpr (Or.inr (Or.inr h))⟩

/-- The nine coordinate blocks specialize the preparation to t=0 and U=b. -/
theorem zero_iff_projective (b : Rat) (hb : b ≠ 0) :
    ZeroPole b ↔ IsSquare (17*b) ∨ IsSquare (-3*(17*b)) ∨
      PoleSurface.ProjectiveSurface (17*b) (Multiplier (17*b) b) :=
  literalAt_iff_projective _ _ (by grind)

end QuarticPole

#print axioms QuarticPole.literalAt_iff_projective
#print axioms QuarticPole.scalar_iff_projective
#print axioms QuarticPole.zero_iff_projective
