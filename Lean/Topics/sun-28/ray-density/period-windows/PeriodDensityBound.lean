import PeriodNormTail

namespace Sun28.PeriodWindows
open Finset Filter
noncomputable section
open scoped Classical

/-- The union bound for all small split primes costs at most one quarter of
the main term in the fixed ray, with no dependence on the guard or cutoff. -/
theorem ray_loss_bound (K R : ℕ) :
    ∑ q∈splitPlaces K R, (2:ℝ)/((q:ℝ)-1)^2 ≤ 1/4 := by
  classical
  let P:=splitPlaces K R
  let j (q:ℕ):=q/4-1
  have idx (q : ℕ) (hq : q∈P) : q=4*(j q+1)+1 := by
    have h := (mem_filter.mp hq).2
    have lo:=h.1.two_le
    dsimp [j]
    omega
  have inj:Set.InjOn j (P:Set ℕ) := fun a ha b hb e=>by rw [idx a ha,idx b hb,e]
  have sub:P.image j⊆range (R+1):=by
    intro t ht
    obtain ⟨q,h,rfl⟩:=mem_image.mp ht
    have upper:=mem_range.mp (mem_filter.mp h).1
    exact mem_range.mpr (by dsimp [j];omega)
  let weight:ℕ→ℝ:=fun t=>2/(4*((t:ℝ)+1))^2
  have same (q:ℕ) (hq:q∈P) : (2:ℝ)/((q:ℝ)-1)^2 = weight (j q) := by
    have eq:= congrArg (fun t:ℕ=>(t:ℝ)) (idx q hq)
    push_cast at eq
    dsimp [weight]
    rw [show (q:ℝ)-1=4*((j q:ℝ)+1) by linarith]
  calc
    _ = ∑ q∈P,weight (j q) := Finset.sum_congr rfl same
    _ = ∑ t∈P.image j,weight t := (Finset.sum_image inj).symm
    _ ≤ ∑ t∈range (R+1),weight t := sum_le_sum_of_subset_of_nonneg sub (by intro t _ _;dsimp [weight];positivity)
    _ ≤ 1/4 := split_loss_quarter (R+1)

/-- Finite level accounting for actual rational norms: bounds for the number
in the base and for the summed discrepancy from the two-ray main terms are
the only analytic quantities at the small primes. -/
theorem clean_lower (K N R : ℕ) (two : 2≤R) (B E : ℝ) (pos : 0≤B)
    (ray : B-E ≤ ((primeBase K N).card:ℝ))
    (errors : ∑ q∈splitPlaces K R, |((selfAt K N q).card:ℝ)-B*(2/((q:ℝ)-1)^2)| ≤ E) :
    3/4*B - 2*E -
      (2*(N.sqrt:ℝ)+1)*(Nat.log 2 (N.sqrt^2+1):ℝ)*((2*(N.sqrt:ℝ)+1)/R+1) ≤ ((cleanSet K N).card:ℝ) := by
  have counts : ((primeBase K N).card:ℝ) ≤ ((cleanSet K N).card:ℝ)+
      (∑ q∈splitPlaces K R,((selfAt K N q).card:ℝ))+((farSelf K N R).card:ℝ):=by exact_mod_cast ray_sieve K N R
  have tail:=far_self_bound K N R two
  have large : ((farSelf K N R).card:ℝ) ≤
      (2*(N.sqrt:ℝ)+1)*(Nat.log 2 (N.sqrt^2+1):ℝ)*((2*(N.sqrt:ℝ)+1)/R+1) := by
    have t := (Rat.cast_le (K:=ℝ)).mpr tail
    push_cast at t
    exact t
  have sum:=Finset.sum_le_sum (s:=splitPlaces K R) (f:=fun q=>((selfAt K N q).card:ℝ))
    (g:=fun q=> B*(2/((q:ℝ)-1)^2)+|((selfAt K N q).card:ℝ)-B*(2/((q:ℝ)-1)^2)|)
    (fun q _ => by linarith [le_abs_self (((selfAt K N q).card:ℝ)-B*(2/((q:ℝ)-1)^2))])
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at sum
  have quarter:=mul_le_mul_of_nonneg_left (ray_loss_bound K R) pos
  linarith

end
end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.ray_loss_bound
#print axioms Sun28.PeriodWindows.clean_lower
