import Mathlib.Tactic

/-! Ramification indices above six distinct geometric points. The geometric
inputs below are the degrees of the six fibres and Riemann–Hurwitz on P¹ in
characteristic zero. -/
namespace ZInQBlueprint.OddBranchPullback

private theorem index_count (E : List ℕ) (pos : ∀ e ∈ E, 0 < e) :
    E.sum = (E.map (· - 1)).sum + E.length ∧
    2 * E.length ≤ E.sum + (E.map (· % 2)).sum := by
  induction E with
  | nil => simp
  | cons e E ih =>
    obtain ⟨eq,le⟩ := ih (fun x hx => pos x (List.mem_cons_of_mem _ hx))
    have he := pos e (List.mem_cons_self (a:=e) (l:=E))
    simp only [List.sum_cons,List.map_cons,List.length_cons]
    omega

/-- At least `2*d+4` points over six distinct targets have odd ramification
index. The list contains all preimages in the six geometric fibres, once each.
The hypotheses are the two numerical consequences of the degree formula and
Riemann–Hurwitz. The final sum counts one per odd index. -/
theorem odd_preimages_six (d : ℕ) (degree_pos : 0 < d) (E : List ℕ)
    (pos : ∀ e ∈ E, 0 < e) (total_degree : E.sum = 6*d)
    (ramification : (E.map (· - 1)).sum ≤ 2*d-2) :
    2*d+4 ≤ (E.map (· % 2)).sum := by
  obtain ⟨eq,le⟩ := index_count E pos
  omega

/-- For five target points the lower bound is `d+4`. Consequently six
prescribed source points suffice for the odd support only if `d ≤ 2`. -/
theorem odd_preimages_five (d : ℕ) (degree_pos : 0 < d) (E : List ℕ)
    (pos : ∀ e ∈ E, 0 < e) (total_degree : E.sum = 5*d)
    (ramification : (E.map (· - 1)).sum ≤ 2*d-2) :
    d+4 ≤ (E.map (· % 2)).sum := by
  obtain ⟨eq,le⟩ := index_count E pos
  omega

end ZInQBlueprint.OddBranchPullback
#print axioms ZInQBlueprint.OddBranchPullback.odd_preimages_six
#print axioms ZInQBlueprint.OddBranchPullback.odd_preimages_five
