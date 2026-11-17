import PartnerQuartic

namespace Sun28.MultiplierChoice
open Sun28.Ordinary Sun28.ScalarHeight Sun28.TwistExtension Sun28.PairedClasses
noncomputable section

theorem partner_symm {μ ν:ℚ} (h : Partner μ ν) : Partner ν μ := by
  rcases h with a|a
  · right; linarith
  · left; linarith

private theorem listed_lower {μ:ℚ} (mem : μ ∈ smallMultipliers) (pos : 0 < μ) : 1 ≤ μ := by
  obtain ⟨⟨g,a,b,i⟩,_,rfl⟩ := Finset.mem_image.mp mem
  change (0:ℚ) < (shift g a b i : ℤ) at pos
  change (1:ℚ) ≤ (shift g a b i : ℤ)
  have hp : (0:ℤ) < shift g a b i := by exact_mod_cast pos
  exact_mod_cast (show 1 ≤ shift g a b i by omega)

/-- Exact positive-half presentation of all the guarded pole branches, with a
choice of second ratio at each positive base. No prescribed squarefree classes enter. -/
theorem pole_iff_positive_menu {B:ℚ} (bp:0<B) (small:B<1/2) :
    polePredicate smallMultipliers B ↔ ∃ μ∈smallMultipliers, 0<μ ∧
      ∃ ν∈smallMultipliers, Partner μ ν ∧
        (Surface (μ*B) (1-B/μ) ∨ Surface (μ*B) (1-B/ν)) := by
  have iff (μ ν:ℚ) (mem:μ∈smallMultipliers) (mp:0<μ) (pair:Partner μ ν) :
      ((∃e z,poleBranch μ B e z) ∨ (∃e z,poleBranch ν B e z)) ↔
        Surface (μ*B) (1-B/μ) ∨ Surface (μ*B) (1-B/ν) :=
    two_branches_iff bp (lt_of_lt_of_le (lt_trans small (by norm_num : (1:ℚ)/2<1)) (listed_lower mem mp))
      (mul_pos mp bp) one_ne_zero (by ring) pair
  constructor
  · rintro (z|⟨w,mem,e,v,ok⟩)
    · exact False.elim (bp.ne' z)
    obtain ⟨t,member,pair⟩ := listed_partner mem
    rcases lt_trichotomy w 0 with neg|z|pos
    · have pt : 0<t := by rcases pair with h|h <;> linarith
      exact ⟨t,member,pt,w,mem,partner_symm pair,(iff t w member pt (partner_symm pair)).mp (Or.inr ⟨e,v,ok⟩)⟩
    · subst w
      obtain ⟨guard,_⟩ := ok
      simp at guard
    · exact ⟨w,mem,pos,t,member,pair,(iff w t mem pos pair).mp (Or.inl ⟨e,v,ok⟩)⟩
  · rintro ⟨w,mem,wp,t,member,pair,h⟩
    rcases (iff w t mem wp pair).mpr h with yes|yes
    · exact Or.inr ⟨w,mem,yes⟩
    · exact Or.inr ⟨t,member,yes⟩
end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.partner_symm
#print axioms Sun28.MultiplierChoice.pole_iff_positive_menu
