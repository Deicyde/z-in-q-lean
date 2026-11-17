import InertAvoidance
import ConductorLoss

namespace Sun28.PrimeLower
open Finset Sun28.MixedSieve Sun28.WeightedSelection Sun28.ContactFactors Sun28.MediumSieve
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime] {ι : Type*}

/-- Any two distinct marked coefficients detect the exceptional rational row through their values. -/
theorem two_values_one {i j : ι} {c : ι → ZMod p} (ij : c i ≠ c j) (u w : ZMod p) :
    (norms c u w i=1 ∧ norms c u w j=1) ↔ (u=1 ∧ w=0) := by
  constructor
  · rintro ⟨v₁,v₂⟩
    unfold norms at v₁ v₂
    have h : (c i-c j)*w^2=0 := by linear_combination v₁-v₂
    have wz : w=0 := (pow_eq_zero_iff (by decide : 2≠0)).mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ij))
    exact ⟨by simpa [wz] using v₁,wz⟩
  · rintro ⟨rfl,rfl⟩
    simp [norms]

def hybrid {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}
    (a : Candidate A d H Y) (T : Finset ℕ) (κ K L : ℕ) : Prop :=
  below a T κ K ∧ ∀ q : ℕ, q.Prime → K<q → q≤L →
    if q%4=3 then ¬((a.u:ZMod q)=1 ∧ (a.v:ZMod q)=0)
    else atPrime a.gaussian T κ q

theorem hybrid_below {A : Fin 3→ℚ} {d κ K L : ℕ} {H Y : ℝ}
    (a : Candidate A d H Y) (T : Finset ℕ) (pos : 0<d)
    (base : exceptionalBound A d ≤ K) (fixed : ∀ q∈T,q≤K)
    (aux : ∀ q∈κ.primeFactors,q≤K) (good : hybrid a T κ K L) : below a T κ L := by
  intro q qp odd seven small
  by_cases atBase : q≤K
  · exact good.1 q qp odd seven atBase
  let _ : Fact q.Prime := ⟨qp⟩
  have h := good.2 q qp (by omega) small
  split at h
  next inert =>
    exact inert_atPrime a pos (by omega) inert (fun mem => atBase (fixed q mem))
      (fun mem => atBase (aux q mem)) h
  next => exact h

def hybridLoss (A : Fin 3→ℚ) (q : ℕ) : ℝ :=
  if hp : q.Prime then
    let _ : Fact q.Prime := ⟨hp⟩
    if q%4=3 then 1-inertRate (coefficients A q)/unitRate (coefficients A q)
    else markedLoss A q
  else 0

theorem hybrid_product (A : Fin 3→ℚ) (S : Finset ℕ) (large : ∀ p∈S,2810≤p) :
    1/2 ≤ ∏ p∈S, (1-hybridLoss A p) := by
  apply uniform_product S _ large
  · intro p hp
    by_cases pr : p.Prime
    · let _ : Fact p.Prime := ⟨pr⟩
      by_cases hi : p%4=3
      · rw [hybridLoss,dite_eq_left pr,ite_eq_left hi]
        let c := coefficients A p
        have k : Fintype.card ↥(shifts A) ≤ 13 := by simpa using Sun28.GaussianSelection.shifts_card_le A
        have half := (inert_relative_loss_le c (by have := large p hp; omega)).1
        apply sub_nonneg.mpr
        apply (div_le_iff₀ (by linarith : 0<unitRate c)).mpr
        rw [one_mul,inert_rate_exact]
        exact sub_le_self _ (by positivity)
      · simpa [hybridLoss,pr,hi,markedLoss] using relative_nonneg (coefficients A p)
    · simp [hybridLoss,pr]
  · intro p hp
    by_cases pr : p.Prime
    · let _ : Fact p.Prime := ⟨pr⟩
      by_cases hi : p%4=3
      · rw [hybridLoss,dite_eq_left pr,ite_eq_left hi]
        have k : Fintype.card ↥(shifts A) ≤ 13 := by simpa using Sun28.GaussianSelection.shifts_card_le A
        have lo := (inert_relative_loss_le (coefficients A p) (by have := large p hp;omega)).2
        have pp : (2:ℝ)<p := by exact_mod_cast (show 2<p by have := large p hp; omega)
        calc
          _ ≤ 2/(p:ℝ)^2 := by linarith
          _ ≤ 2/((p:ℝ)-1)^2 := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (by linarith)) (by nlinarith)
          _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
      · simpa [hybridLoss,pr,hi] using marked_bound A p (large p hp)
    · simp [hybridLoss,pr]
      positivity

end
end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.two_values_one
#print axioms Sun28.PrimeLower.hybrid_below
#print axioms Sun28.PrimeLower.hybrid_product
