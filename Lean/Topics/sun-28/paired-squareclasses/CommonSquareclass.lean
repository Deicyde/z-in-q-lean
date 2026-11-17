import TwistParameter

namespace Sun28.PairedClasses
open PreparedPoles ZInQ.RouteK

/-- Precisely the conclusion in the manuscript, with Mathlib squarefreeness. -/
def Realized (β θ : ℕ) : Prop :=
  ∃ n : ℕ, 0<n ∧ Squarefree n ∧ n.Coprime (6*θ) ∧
    TwistPoint β n ∧ TwistPoint β (n*θ)

/-- A single equation for the directions of the two scaled conics.  The
squarefree part in the coprimality test is a function of the first direction. -/
def Common (β θ : ℕ) : Prop :=
  ∃ u v U V z : ℚ, 0 < (β:ℚ)*quartic β u v ∧
    (sqf ((β:ℚ)*quartic β u v)).natAbs.Coprime (6*θ) ∧
    (θ:ℚ)*quartic β u v = quartic β U V*z^2

theorem realized_iff_common {β θ : ℕ} (hb : 0<β) (hθ : 0<θ) :
    Realized β θ ↔ Common β θ := by
  have bp : 0<(β:ℚ) := by exact_mod_cast hb
  have tp : 0<(θ:ℚ) := by exact_mod_cast hθ
  constructor
  · rintro ⟨n,hn,hs,hc,h₁,h₂⟩
    have np : 0<(n:ℚ) := by exact_mod_cast hn
    obtain ⟨u,v,w,e⟩ := (twist_iff_quartic hb hn).mp h₁
    obtain ⟨U,V,W,E⟩ := (twist_iff_quartic hb (Nat.mul_pos hn hθ)).mp h₂
    push_cast at E
    have wn : w≠0 := by rintro rfl; simp at e; exact hn.ne' e
    have ap : 0 < (β:ℚ)*quartic β u v := pos_of_mul_pos_left (e ▸ np) (sq_nonneg w)
    have kernel : sqf ((β:ℚ)*quartic β u v) = (n:ℤ) := by
      apply sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr hs) (inv_ne_zero wn)
      push_cast
      rw [e]
      field_simp
    refine ⟨u,v,U,V,W/w,ap,by simpa only [kernel,Int.natAbs_natCast] using hc,?_⟩
    rw [e] at E
    field_simp [wn]
    apply mul_left_cancel₀ bp.ne'
    linear_combination E
  · rintro ⟨u,v,U,V,z,ap,hc,relation⟩
    let n := (sqf ((β:ℚ)*quartic β u v)).natAbs
    have kp := (sqf_pos_iff ap.ne').mpr ap
    have castN : (n:ℤ) = sqf ((β:ℚ)*quartic β u v) := Int.natAbs_of_nonneg kp.le
    have castQ : (n:ℚ) = (sqf ((β:ℚ)*quartic β u v):ℚ) := by exact_mod_cast castN
    have hn : 0<n := by exact_mod_cast (show (0:ℤ)<n by rwa [castN])
    obtain ⟨sf,s,hs,eq⟩ := sqf_spec ap.ne'
    have eqN : (n:ℚ) = β*quartic β u v*(s⁻¹)^2 := by
      rw [eq,castQ]
      field_simp
    have first := (twist_iff_quartic hb hn).mpr ⟨u,v,s⁻¹,eqN⟩
    refine ⟨n,hn,Int.squarefree_natAbs.mpr sf,hc,first,(twist_iff_quartic hb (Nat.mul_pos hn hθ)).mpr ?_⟩
    refine ⟨U,V,z*s⁻¹,?_⟩
    push_cast
    rw [eqN]
    linear_combination (β:ℚ)*(s⁻¹)^2*relation

end Sun28.PairedClasses
#print axioms Sun28.PairedClasses.realized_iff_common
