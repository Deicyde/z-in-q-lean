import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! The last lower ramification group and the two different exponents in a tower. -/
namespace ZInQBlueprint.WildLevel
open Finset
noncomputable section

/-- The wild part of the inverse Herbrand sum, with the factor |G₀| restored.
Each summand is the order of one nontrivial lower ramification group. -/
def herbrandNumerator (g : List ℕ) := g.sum

/-- Hilbert's sum omits the identity in each group. -/
theorem hilbert_sum (g : List ℕ) (positive : ∀ k∈g, 1≤k) :
    (g.map (·-1)).sum + g.length = herbrandNumerator g := by
  induction g with
  | nil => simp [herbrandNumerator]
  | cons a t ih =>
    have ha := positive a (by simp)
    have h := ih (fun k hk => positive k (by simp [hk]))
    simp only [herbrandNumerator,List.map_cons,List.sum_cons,List.length_cons] at h ⊢
    omega

/-- A cyclic subgroup of order p in the last lower group yields the two
different exponents d₀ and d₁. The equations are Hilbert's different,
transitivity, and the cyclic prime-degree different respectively. The
inequalities are the Eisenstein derivative bounds at the two levels. -/
theorem last_slope {p e₀ m d₀ d₁ : ℕ} (g : List ℕ)
    (primeSize : 2≤p) (ePos : 0<e₀) (wild : 1≤m)
    (positive : ∀ k∈g, 1≤k)
    (tower : p*e₀-1+(g.map (·-1)).sum = d₁+p*d₀)
    (cyclic : d₁=(g.length+1)*(p-1))
    (base : d₀≤e₀-1+e₀*(m-1)) (top : d₁≤p-1+p*e₀) :
    (p-1)*(p*e₀+herbrandNumerator g) ≤ p*e₀*((p-1)*m+p) := by
  have count := hilbert_sum g positive
  have pp : 0<p:=by omega
  have ep : 0<p*e₀:=Nat.mul_pos pp ePos
  zify [show 1≤p*e₀ by omega,show 1≤p by omega,show 1≤e₀ by omega,wild] at tower cyclic base top count ⊢
  have ident : (p-1:ℤ)*((p:ℤ)*e₀+herbrandNumerator g) =
      (p:ℤ)*(p-1)*d₀+(p:ℤ)*d₁ := by
    linear_combination (p-1:ℤ)*tower - (p-1:ℤ)*count - cyclic
  have ppInt : (2:ℤ)≤p := by exact_mod_cast primeSize
  have scale : 0≤(p:ℤ)*(p-1):=mul_nonneg (by omega) (by omega)
  calc _ = _ := ident
       _ ≤ (p:ℤ)*(p-1)*(e₀-1+e₀*(m-1))+(p:ℤ)*(p-1+p*e₀) :=
          add_le_add (mul_le_mul_of_nonneg_left base scale) (mul_le_mul_of_nonneg_left top (by positivity))
       _ = _ := by ring

/-- A two-dimensional Artin conductor has tame term at most two. After
multiplication by e its Swan term is bounded by twice the Herbrand numerator.
This also allows a residual field detecting only positive groups. -/
theorem conductor_from_last {p e₀ m a : ℕ} (g : List ℕ) (hp:2≤p) (he:0<e₀)
    (slope : (p-1)*(p*e₀+herbrandNumerator g) ≤ p*e₀*((p-1)*m+p))
    (artin : p*e₀*a ≤ 2*(p*e₀+herbrandNumerator g)) :
    (p-1)*a ≤ 2*((p-1)*m+p) := by
  have epos := Nat.mul_pos (show 0<p by omega) he
  apply Nat.le_of_mul_le_mul_left _ epos
  calc
    p*e₀*((p-1)*a) = (p-1)*(p*e₀*a) := by ring
    _ ≤ (p-1)*(2*(p*e₀+herbrandNumerator g)) := Nat.mul_le_mul_left _ artin
    _ = 2*((p-1)*(p*e₀+herbrandNumerator g)) := by ring
    _ ≤ 2*(p*e₀*((p-1)*m+p)) := Nat.mul_le_mul_left 2 slope
    _ = _ := by ring

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.hilbert_sum
#print axioms ZInQBlueprint.WildLevel.last_slope
#print axioms ZInQBlueprint.WildLevel.conductor_from_last
