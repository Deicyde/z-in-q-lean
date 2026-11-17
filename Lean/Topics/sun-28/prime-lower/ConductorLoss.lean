import CutoffProduct

namespace Sun28.PrimeLower
open Finset Sun28.MixedSieve
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]

/-- Ordinary unit rows after excluding the single pair (u,w)=(1,0). -/
def inertRate (c : ι → ZMod p) : ℝ :=
  (∑ w : ZMod p, ∑ u : ZMod p,
    if (∀ i, norms c u w i ≠ 0) ∧ ¬ (u=1 ∧ w=0) then (1:ℝ) else 0) / (p:ℝ)^2

theorem inert_rate_exact (c : ι → ZMod p) :
    inertRate c = unitRate c - 1/(p:ℝ)^2 := by
  classical
  have one (w u : ZMod p) :
      (if (∀ i,norms c u w i≠0) ∧ ¬(u=1 ∧ w=0) then (1:ℝ) else 0) =
      (if ∀ i,norms c u w i≠0 then 1 else 0) -
      (if w=0 then (if u=1 then 1 else 0) else 0) := by
    by_cases hw : w=0
    · by_cases hu : u=1
      · subst w; subst u; simp [norms]
      · simp only [hw,hu,not_false_eq_true,and_true,ite_false,ite_true,sub_zero]
    · simp only [hw,and_false,not_false_eq_true,and_true,ite_false,sub_zero]
  unfold inertRate unitRate
  simp_rw [one,Finset.sum_sub_distrib]
  have singleton : (∑ w : ZMod p, ∑ u : ZMod p, if w=0 then (if u=1 then (1:ℝ) else 0) else 0)=1 := by
    simp [Finset.sum_ite_irrel]
  rw [singleton,sub_div]

theorem inert_relative_loss_le (c : ι → ZMod p) (big : 2 * Fintype.card ι ≤ p) :
    1/2 ≤ unitRate c ∧ 1 - 2/(p:ℝ)^2 ≤ inertRate c / unitRate c := by
  have pp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr : 2 * (Fintype.card ι : ℝ) ≤ p := by exact_mod_cast big
  have lo := units_lower c
  have small : (Fintype.card ι : ℝ)/p ≤ 1/2 := (div_le_iff₀ pp).mpr (by linarith)
  have half : 1/2≤unitRate c := by linarith
  refine ⟨half,(le_div_iff₀ (by linarith : 0<unitRate c)).mpr ?_⟩
  rw [inert_rate_exact]
  calc
    (1-2/(p:ℝ)^2)*unitRate c = unitRate c - (2*unitRate c)/(p:ℝ)^2 := by ring
    _ ≤ _ := sub_le_sub_left (div_le_div_of_nonneg_right (by linarith : 1≤2*unitRate c) (by positivity)) _

/-- The elementary telescope is valid over all integers, hence for any finite set of
primes; the constant is independent of the last ray conductor. -/
theorem rational_factors (S : Finset ℕ) (big : ∀ p∈S,5≤p) :
    (1:ℝ)/2 ≤ ∏ p∈S, (1 - 2/(p:ℝ)^2) := by
  let N := S.sup id+1
  let g (j : ℕ) : ℝ := 2/(4+(j:ℝ)) - 2/(4+(j:ℝ)+1)
  have part (n : ℕ) : ∑ j∈range n,g j = 1/2 - 2/(4+(n:ℝ)) := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [sum_range_succ,ih]; dsimp [g]; push_cast; ring
  have gp (j : ℕ) : 0≤g j := by
    dsimp [g]; apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  let R := S.image (fun p => p-5)
  have sub : R ⊆ range N := by
    intro j hj
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
    have le : p≤S.sup id := Finset.le_sup (f:=id) hp
    exact mem_range.mpr (by dsimp [N]; omega)
  have cap (p) (hp : p∈S) : 2/(p:ℝ)^2 ≤ g (p-5) := by
    have pp := big p hp
    have pr : (5:ℝ)≤p := by exact_mod_cast pp
    have e : ((p-5:ℕ):ℝ) = (p:ℝ)-5 := by rw [Nat.cast_sub pp]; norm_num
    dsimp [g]; rw [e]
    rw [show 4+((p:ℝ)-5)=p-1 by ring,show (p:ℝ)-1+1=p by ring]
    have pos : (0:ℝ)<p := by linarith
    have low : (0:ℝ)<p-1 := by linarith
    rw [show 2/((p:ℝ)-1)-2/p = 2/((p-1)*p) by field_simp; ring]
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos low pos)
    nlinarith
  have ss : (∑ p∈S,2/(p:ℝ)^2) ≤ 1/2 := by
    calc
      _ ≤ ∑ p∈S,g (p-5) := sum_le_sum cap
      _ = ∑ j∈R,g j := by
        rw [show R=S.image (fun p => p-5) from rfl,Finset.sum_image]
        intro a ha b hb eq
        have := big a ha
        have := big b hb
        change a-5=b-5 at eq
        omega
      _ ≤ ∑ j∈range N,g j := Finset.sum_le_sum_of_subset_of_nonneg sub (fun j _ _ => gp j)
      _ ≤ 1/2 := by rw [part]; exact sub_le_self _ (by positivity)
  apply (show 1/(2:ℝ) ≤ 1 - ∑ p ∈ S,2/(p:ℝ)^2 by linarith).trans
  apply product_good _ _ (by intros; positivity)
  intro p hp
  have pr : (5:ℝ)≤p := by exact_mod_cast big p hp
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0:ℝ)<p))).mpr
  nlinarith

end
end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.inert_rate_exact
#print axioms Sun28.PrimeLower.inert_relative_loss_le
#print axioms Sun28.PrimeLower.rational_factors
