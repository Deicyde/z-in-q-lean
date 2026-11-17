import FiniteGrid

namespace Sun28.PrimeTransfer
open Finset
open scoped Classical
noncomputable section
variable {n : ℕ} [NeZero n]

def circleMass (c : Finset ℤ) (g : ZMod n → ℝ) (H : ZMod n) (W : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 W ×ˢ (univ : Finset (ZMod n))),
    ∏ h ∈ c, g (p.2 + H * (h:ZMod n) * (p.1:ZMod n)^2)

def denseLevel (g : ZMod n → ℝ) (a : ℝ) := univ.filter fun x => a ≤ g x

theorem level_density (g : ZMod n → ℝ) {a C : ℝ} {s : ℕ} (ha : 0 < a)
    (bound : ∀ x, g x ≤ C) (density : 2*a*n ≤ ∑ x, g x) (hs : C ≤ a*s) :
    n ≤ s * (denseLevel g a).card := by
  classical
  let E := denseLevel g a
  have per (x : ZMod n) : g x ≤ a + if x ∈ E then C else 0 := by
    by_cases hx : x∈E
    · simp only [ite_eq_left hx]; linarith [bound x]
    · have := lt_of_not_ge (show ¬a ≤ g x by simpa [E,denseLevel] using hx)
      simp only [ite_eq_right hx,add_zero]; linarith
  have total := sum_le_sum (s:=univ) (fun x _ => per x)
  rw [sum_add_distrib,←Finset.sum_filter] at total
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul,filter_mem_eq_inter,univ_inter] at total
  have target : (n:ℝ) ≤ s*(E.card:ℝ) := by
    apply le_of_mul_le_mul_left (a:=a) _ ha
    nlinarith only [density,total,mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α:=ℝ) E.card)]
  exact_mod_cast target

/-- A bounded dense weight gives a positive count on every sufficiently long step interval. -/
theorem bounded_grid_lower (c : Finset ℤ) (g : ZMod n → ℝ) (H : ZMod n)
    {a C : ℝ} {s B W : ℕ} (ha : 0 < a) (gpos : ∀ x, 0 ≤ g x)
    (bound : ∀ x, g x ≤ C) (density : 2*a*n ≤ ∑ x, g x) (hs : C ≤ a*s)
    (hB : 0 < B) (recurs : Recurrent c s B) (width : 2*B ≤ W) :
    a^c.card * (n:ℝ)*W ≤ (4*s*B^3 : ℕ) * circleMass c g H W := by
  classical
  let E := denseLevel g a
  let P := patterns c E H W
  have card := grid_lower c E H hB recurs (level_density g ha bound density hs) width
  let F (p : ℕ × ZMod n) := ∏ h∈c, g (p.2+H*(h:ZMod n)*(p.1:ZMod n)^2)
  have small (p : ℕ × ZMod n) (hp : p∈P) : a^c.card ≤ F p := by
    have v := (mem_filter.mp hp).2
    rw [←prod_const (s:=c)]
    exact prod_le_prod₀ (fun _ _ => ha.le) (fun h hh => (mem_filter.mp (v h hh)).2)
  have weighted : (P.card:ℝ)*a^c.card ≤ circleMass c g H W := by
    calc
      _ = ∑ _p∈P, a^c.card := by simp
      _ ≤ ∑ p∈P,F p := sum_le_sum small
      _ ≤ circleMass c g H W := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x _ _ => prod_nonneg fun h _ => gpos _)
  have cR : (n:ℝ)*W ≤ (4*s*B^3:ℕ)*(P.card:ℝ) := by exact_mod_cast card
  calc
    _ = a^c.card*((n:ℝ)*W) := by ring
    _ ≤ a^c.card*((4*s*B^3:ℕ)*(P.card:ℝ)) := mul_le_mul_of_nonneg_left cR (pow_nonneg ha.le _)
    _ = (4*s*B^3:ℕ)*((P.card:ℝ)*a^c.card) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left weighted (by positivity)

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.level_density
#print axioms Sun28.PrimeTransfer.bounded_grid_lower
