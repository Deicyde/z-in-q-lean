import GaussianWindow

namespace Sun28.PrimeModel
open Finset Sun28.PrimeTransfer
open scoped Classical
noncomputable section

/-- The support of the actual dyadic central prime window. -/
def inWindow {n : ℕ} (b V N : ℕ) (x : ZMod n) : Prop :=
  N/2 < b+V*x.val ∧ b+V*x.val ≤ N ∧ n ≤ 4*x.val ∧ 4*x.val < 3*n

/-- Centering by the matching interval profile commutes with restriction. -/
theorem supported_center {n : ℕ} [NeZero n] (μ : ℝ) (K b V N : ℕ) (x : ZMod n) :
    (V.totient:ℝ)/V*window K b V N x - (if inWindow b V N x then μ else 0) =
    if inWindow b V N x then (V.totient:ℝ)/V*classWeight K (b+V*x.val)-μ else 0 := by
  classical
  change _ - (if _ then _ else _) = _
  unfold window inWindow
  split <;> simp_all

/-- After making independent copies of the parameter tuple, two forms have constant
difference exactly when both individual polynomials (or even just functions) are constant. -/
theorem independent_copies {α β : Type*} [Nonempty α] [Nonempty β] (f : α→ℤ) (g : β→ℤ) :
    (∃ e, ∀ m m', f m - g m' = e) ↔
    (∃ a, ∀ m, f m = a) ∧ (∃ b, ∀ m', g m' = b) := by
  obtain ⟨i⟩ := ‹Nonempty α›
  obtain ⟨j⟩ := ‹Nonempty β›
  constructor
  · rintro ⟨e,h⟩
    refine ⟨⟨f i, fun m => ?_⟩,⟨g j,fun m => ?_⟩⟩
    · linarith [h m j,h i j]
    · linarith [h i m,h i j]
  · rintro ⟨⟨a,A⟩,⟨b,B⟩⟩
    exact ⟨a-b, fun m m' => by rw [A,B]⟩

/-- For a single base factor and independent copies of all other factors, the
localized error is controlled by the three global moments with the base appearing once. -/
theorem one_base_variance {Ω : Type*} (C S : Finset Ω) (sub : C⊆S)
    (g H : Ω→ℝ) (pos : ∀ x∈S, 0 ≤ g x) :
    ((∑ x∈C, g x*H x) - ∑ x∈C, g x)^2 ≤
    (∑ x∈C, g x) *
      ((∑ x∈S, g x*(H x)^2)-2*(∑ x∈S,g x*H x)+ ∑ x∈S,g x) := by
  classical
  have cs := sum_sq_le_sum_mul_sum_of_sq_le_mul (R:=ℝ) C
    (r:=fun x => g x*(H x-1)) (f:=g) (g:=fun x => g x*(H x-1)^2)
    (fun x hx => pos x (sub hx)) (fun x hx => mul_nonneg (pos x (sub hx)) (sq_nonneg _))
    (fun x _ => (by ring : (g x*(H x-1))^2=g x*(g x*(H x-1)^2)).le)
  have vs : (∑ x∈C, g x*(H x-1)^2) ≤ ∑ x∈S, g x*(H x-1)^2 :=
    sum_le_sum_of_subset_of_nonneg sub (fun x hx _ => mul_nonneg (pos x hx) (sq_nonneg _))
  have expand : (∑ x∈S, g x*(H x-1)^2) =
      (∑ x∈S, g x*(H x)^2)-2*(∑ x∈S,g x*H x)+ ∑ x∈S,g x := by
    rw [Finset.mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro x _
    ring
  rw [←expand,←sum_sub_distrib]
  simp_rw [mul_sub, mul_one] at cs
  exact cs.trans (mul_le_mul_of_nonneg_left vs (sum_nonneg (fun x hx => pos x (sub hx))))

end
end Sun28.PrimeModel
#print axioms Sun28.PrimeModel.supported_center
#print axioms Sun28.PrimeModel.independent_copies
#print axioms Sun28.PrimeModel.one_base_variance
