import CommonSquareclass

namespace Sun28.PairedClasses
open PreparedPoles ZInQ.RouteK

/-- This quartic family fixes the common parameter to β. -/
def Family (β θ : ℕ) : Prop := ∃ k h : ℚ, h≠0 ∧
  (k^2-β)*(9*k^2-β) = θ*h^2

theorem quartic_specialization (b k : ℚ) :
    quartic b (3*k^2-b) (2*k) = (k^2-b)*(9*k^2-b)*(3*k^2+b)^2 := by
  unfold quartic
  ring

theorem realized_of_family {β θ : ℕ} (hb : 0<β) (hθ : 0<θ)
    (hβ : Squarefree β) (hc : β.Coprime (6*θ)) (h : Family β θ) : Realized β θ := by
  obtain ⟨k,y,hy,e⟩ := h
  have bp : 0<(β:ℚ) := by exact_mod_cast hb
  have H : 3*k^2+(β:ℚ) ≠ 0 := ne_of_gt (by positivity)
  refine ⟨β,hb,hβ,hc,⟨1,0,one_ne_zero,by norm_num⟩,
    (twist_iff_quartic hb (Nat.mul_pos hb hθ)).mpr ?_⟩
  refine ⟨3*k^2-β,2*k,(y*(3*k^2+β))⁻¹,?_⟩
  push_cast
  rw [quartic_specialization,e]
  field_simp

theorem diagonal {β : ℕ} (hb : 0<β) (hs : Squarefree β) (hc : β.Coprime 6) :
    Realized β 1 :=
  ⟨β,hb,hs,by simpa using hc,⟨1,0,one_ne_zero,by norm_num⟩,
    ⟨1,0,one_ne_zero,by norm_num⟩⟩

def ZeroOrdinate (β l : ℕ) : Prop := ∃ t : ℚ, t≠0 ∧
  let x := (β:ℚ)*t^2
  (0:ℚ) = x*(x-l)*(x+3*l)

private theorem zero_scale {β l : ℕ} (hb : 0<β) (hl : 0<l) (h : ZeroOrdinate β l) :
    ∃ t : ℚ, t≠0 ∧ (l:ℚ)=β*t^2 := by
  obtain ⟨t,ht,eq⟩ := h
  have bp : 0<(β:ℚ) := by exact_mod_cast hb
  have lp : 0<(l:ℚ) := by exact_mod_cast hl
  have xp : 0 < (β:ℚ)*t^2 := mul_pos bp (sq_pos_of_ne_zero ht)
  dsimp at eq
  rcases mul_eq_zero.mp eq.symm with e | e
  · exact ⟨t,ht,(sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left xp.ne')).symm⟩
  · linarith

theorem two_zero_ordinates {β n θ : ℕ} (hb : 0<β) (hn : 0<n) (ht : 0<θ)
    (hs : Squarefree θ) (first : ZeroOrdinate β n) (second : ZeroOrdinate β (n*θ)) :
    θ=1 := by
  obtain ⟨u,hu,e⟩ := zero_scale hb hn first
  obtain ⟨v,hv,f⟩ := zero_scale hb (Nat.mul_pos hn ht) second
  have bp : (β:ℚ)≠0 := by exact_mod_cast hb.ne'
  push_cast at f
  rw [e] at f
  have rel : (θ:ℚ) = (1:ℤ)*(v/u)^2 := by
    push_cast
    rw [one_mul,div_pow,eq_div_iff (pow_ne_zero 2 hu)]
    apply mul_left_cancel₀ bp
    linear_combination f
  have one := sqf_eq_of_eq_mul_sq (d:=(1:ℤ)) squarefree_one (div_ne_zero hv hu) rel
  have same := sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr hs) (t:=(1:ℚ)) one_ne_zero
    (show (θ:ℚ) = (θ:ℤ)*(1:ℚ)^2 by simp)
  exact_mod_cast same.symm.trans one

/-- The remaining assertion includes just parameters outside the explicit
quartic family. The common direction equation and a coprimality test are the
only requirements on its witness. -/
def Residual : Prop :=
  ∀ β θ : ℕ, 0<β → 0<θ → Squarefree β → Squarefree θ →
    β.Coprime θ → β.Coprime 6 → θ.Coprime 6 → β%24=17 → θ%24=1 →
    (∀ p : ℕ, p.Prime → p∣θ → LocalSquareAt p β) →
    (∀ p : ℕ, p.Prime → p∣β → LocalSquareAt p θ) →
    θ≠1 → ¬Family β θ → Common β θ

theorem simultaneous_of_residual (remaining : Residual) :
    ManuscriptV15.Arithmetic.SimultaneousTwists := by
  apply twists_iff_manuscript.mp
  intro β θ hb ht sb st bc b6 t6 bm tm locB locT
  change Realized β θ
  by_cases diag : θ=1
  · subst θ; exact diagonal hb sb b6
  by_cases fam : Family β θ
  · exact realized_of_family hb ht sb (b6.mul_right bc) fam
  · exact (realized_iff_common hb ht).mpr (remaining β θ hb ht sb st bc b6 t6 bm tm locB locT diag fam)

theorem residual_of_simultaneous (full : ManuscriptV15.Arithmetic.SimultaneousTwists) :
    Residual := by
  intro β θ hb ht sb st bc b6 t6 bm tm locB locT _ _
  exact (realized_iff_common hb ht).mp
    (twists_iff_manuscript.mpr full β θ hb ht sb st bc b6 t6 bm tm locB locT)

end Sun28.PairedClasses
#print axioms Sun28.PairedClasses.quartic_specialization
#print axioms Sun28.PairedClasses.realized_of_family
#print axioms Sun28.PairedClasses.diagonal
#print axioms Sun28.PairedClasses.two_zero_ordinates
#print axioms Sun28.PairedClasses.simultaneous_of_residual
#print axioms Sun28.PairedClasses.residual_of_simultaneous
