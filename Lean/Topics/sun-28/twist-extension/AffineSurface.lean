import SignedSurface

namespace Sun28.TwistExtension
open PairedClasses
noncomputable section

def fibrePolynomial (b t : ℚ) := quartic b t (t+1)

def AffineSurface (b θ : ℚ) : Prop := ∃ t s w : ℚ, w≠0 ∧
  w^2=θ*fibrePolynomial b t*fibrePolynomial b s

private theorem chart_at {b u v : ℚ} (n : v-u≠0) :
    fibrePolynomial b (u/(v-u))*(v-u)^4=quartic b u v := by
  unfold fibrePolynomial quartic
  field_simp
  ring

private theorem chart {b u v : ℚ} (live : quartic b u v≠0) :
    ∃ t c : ℚ,c≠0 ∧ fibrePolynomial b t*c^4=quartic b u v := by
  by_cases nz : v-u≠0
  · exact ⟨u/(v-u),v-u,nz,chart_at nz⟩
  have ne : v-(-u)≠0 := by
    intro zero
    have e : u=0:=by simp only [not_not] at nz; linarith only [zero,nz]
    have f : v=0:=by simp only [not_not] at nz;linarith
    exact live (by simp [quartic,e,f])
  refine ⟨-u/(v-(-u)),v-(-u),ne,?_⟩
  rw [chart_at ne];simp [quartic]

theorem affine_iff_surface {b θ : ℚ} : AffineSurface b θ ↔ Surface b θ := by
  constructor
  · rintro ⟨t,s,w,wn,e⟩;exact ⟨t,t+1,s,s+1,w,wn,e⟩
  · rintro ⟨u,v,U,V,W,wn,e⟩
    have prod : θ*quartic b u v*quartic b U V≠0:=e ▸ pow_ne_zero 2 wn
    obtain ⟨t,c,cn,f⟩:=chart (right_ne_zero_of_mul (left_ne_zero_of_mul prod))
    obtain ⟨s,d,dn,g⟩:=chart (right_ne_zero_of_mul prod)
    refine ⟨t,s,W/(c*d)^2,div_ne_zero wn (pow_ne_zero _ (mul_ne_zero cn dn)),?_⟩
    rw [←f,←g] at e
    field_simp
    linear_combination e

end
end Sun28.TwistExtension
#print axioms Sun28.TwistExtension.affine_iff_surface
