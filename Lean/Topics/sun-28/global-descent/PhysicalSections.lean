import MarkedOrbit

namespace Sun28.GlobalDescent
open Sun28.GlobalSections
noncomputable section

def firstValue (r:ℚ) := (1-r)*(3*r+1)
def secondValue (r:ℚ) := 3*(1-r)*(r+3)

/-- A square on either of two explicit elliptic quartics in the physical ratio. -/
def TwoSections (b r : ℚ) : Prop := IsSquare (b*firstValue r) ∨ IsSquare (b*secondValue r)

theorem first_mark {r b:ℚ} (lo:0<r) (hi:r<1) (bp:0<b) (h:IsSquare (b*firstValue r)) :
    represented b r := by
  obtain ⟨k,hk⟩:=h
  have f:0<firstValue r:=by unfold firstValue; positivity [(sub_pos.mpr hi)]
  have k0:k≠0:=fun e=> (mul_pos bp f).ne' (by simpa [e] using hk)
  have d:= (orbit_right lo hi one_ne_zero (identity_class lo hi))
  have dd:Mark r (-rightRoot r):=by simpa using d
  have div : b*lead r=(-rightRoot r)*(k/(3*r+1))^2 := by
    have nz:3*r+1≠0:=by positivity
    field_simp
    unfold lead rightRoot firstValue at *
    linear_combination -(r+3)*(3*r+1)*hk
  rw [represented_iff,div]
  exact (rescale (div_ne_zero k0 (by positivity : 3*r+1≠0))).mp dd

theorem second_mark {r b:ℚ} (lo:0<r) (hi:r<1) (bp:0<b) (h:IsSquare (b*secondValue r)) :
    represented b r := by
  obtain ⟨k,hk⟩:=h
  have f:0<secondValue r:=by unfold secondValue;positivity [(sub_pos.mpr hi)]
  have k0:k≠0:=fun e=> (mul_pos bp f).ne' (by simpa [e] using hk)
  have d:=orbit_left lo hi one_ne_zero (identity_class lo hi)
  have dd:Mark r (-leftRoot r):=by simpa using d
  have div:b*lead r=(-leftRoot r)*(k/(3*(r-1)))^2 := by
    have nz:r-1≠0:=sub_ne_zero.mpr hi.ne
    field_simp
    unfold lead leftRoot secondValue at *
    linear_combination -3*(r-1)^2*hk
  rw [represented_iff,div]
  exact (rescale (div_ne_zero k0 (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hi.ne)))).mp dd

theorem represented_of_tests {r b:ℚ} (lo:0<r) (hi:r<1) (bp:0<b) (h:TwoSections b r) :
    represented b r := h.elim (first_mark lo hi bp) (second_mark lo hi bp)

theorem normalized_pair {b θ s:ℚ} (tn:θ≠0) :
    TwoSections b (s^2/θ) ↔
      IsSquare (b*(θ-s^2)*(3*s^2+θ)) ∨ IsSquare (3*b*(θ-s^2)*(s^2+3*θ)) := by
  have mul_square (u v:ℚ) (e:u*θ^2=v) : IsSquare u ↔ IsSquare v := by
    constructor
    · rintro ⟨k,h⟩;refine ⟨k*θ,?_⟩;rw [←e,h];ring
    · rintro ⟨k,h⟩;refine ⟨k/θ,?_⟩;field_simp;linear_combination e.trans h
  exact or_congr (mul_square _ _ (by unfold firstValue;field_simp))
    (mul_square _ _ (by unfold secondValue;field_simp))

end
end Sun28.GlobalDescent
#print axioms Sun28.GlobalDescent.first_mark
#print axioms Sun28.GlobalDescent.second_mark
#print axioms Sun28.GlobalDescent.represented_of_tests
#print axioms Sun28.GlobalDescent.normalized_pair
