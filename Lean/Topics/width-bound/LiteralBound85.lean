import LiteralTower314
import Mathlib.Tactic.Positivity

open MvPolynomial Sun28.Branches
namespace WidthTower.Literal314
noncomputable section

/-- Keep the input in position zero and insert two fresh witnesses after it. -/
private def embed : Fin 83 → Fin 85 :=
  Fin.cases 0 (fun i : Fin 82 => i.succ.succ.succ)

def polynomial85 : Poly 85 :=
  (rename embed polynomial83)^2 + (X ((0 : Fin 84).succ))^2 +
    (X ((0 : Fin 83).succ.succ))^2

private theorem at85 (t a b : ℚ) (z : Fin 82 → ℚ) :
    value (Fin.cases t (Fin.cases a (Fin.cases b z))) polynomial85 =
      (value (Fin.cases t z) polynomial83)^2 + a^2 + b^2 := by
  let p : Fin 85 → ℚ := Fin.cases t (Fin.cases a (Fin.cases b z))
  have rename_eval : value p (rename embed polynomial83) = value (Fin.cases t z) polynomial83 := by
    unfold value
    change eval₂ _ _ (rename _ _) = eval₂ _ _ _
    rw [eval₂_rename]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hu : value p (X (0 : Fin 84).succ) = a := by
    change eval₂ (Int.castRingHom ℚ) p (X (0 : Fin 84).succ) = a
    rw [eval₂_X]
    rfl
  have hv : value p (X (0 : Fin 83).succ.succ) = b := by
    change eval₂ (Int.castRingHom ℚ) p (X (0 : Fin 83).succ.succ) = b
    rw [eval₂_X]
    rfl
  change value p polynomial85 = _
  simp only [polynomial85, map_add, map_pow, rename_eval, hu, hv]

/-- Exact arity, with both extra coordinates constrained at every rational zero. -/
theorem projection85 (x : ℚ) :
    (∃ w : Fin 84 → ℚ, value (Fin.cases x w) polynomial85 = 0) ↔ admits x := by
  rw [← projection83]
  constructor
  · rintro ⟨w,hw⟩
    let z := Fin.tail (Fin.tail w)
    have split : Fin.cases (w 0) (Fin.cases (Fin.tail w 0) z) = w := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    rw [← split, at85] at hw
    refine ⟨z, ?_⟩
    nlinarith [sq_nonneg (value (Fin.cases x z) polynomial83),
               sq_nonneg (w 0), sq_nonneg (Fin.tail w 0)]
  · rintro ⟨z,hz⟩
    exact ⟨Fin.cases 0 (Fin.cases 0 z), by rw [at85,hz]; norm_num⟩

end
end WidthTower.Literal314
#print axioms WidthTower.Literal314.projection85
