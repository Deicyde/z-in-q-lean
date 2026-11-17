import LogCutoff
import PublishedProjection

namespace Sun28.MediumSieve
open Sun28.SinglePrime Sun28.ContactFactors Sun28.WeightedSelection Sun28.ContactSieve Filter Topology
open scoped Classical
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

/-- Only sufficiently narrow rows are needed. The first row can depend on the fixed cutoff. -/
def LogRow (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ L J : ℕ) (C : ℝ) : Prop :=
  ∀ j : ℕ,J≤j → ∀ᶠ t : ℕ in atTop,
    let N:=lengthAt t
    let W:=rowWidth j N
    middleMass T κ L (logCutoff A t) (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W)≤
      (C/(L:ℝ)+1/((j:ℝ)+1))*((N:ℝ)*W)

theorem log_surplus {T : Finset ℕ} {κ K L J : ℕ} {σ C : ℝ}
    (base : CountThreshold A d H Y T κ K L σ) (middle : LogRow A d H Y T κ L J C)
    (big : 2810≤K) (kl : K≤L) (inT : ∀ p∈T,p≤K) (inAux : ∀ p∈κ.primeFactors,p≤K)
    (sig : 0<σ) (margin : C/(L:ℝ)<σ/8) :
    ∃ S : Finset (Record A d H Y),surplus T κ L S := by
  obtain ⟨ω,slow,counts⟩:=base
  let pred := fun j b=>J≤j → ∀ t : ℕ,b=lengthAt t →
    middleMass T κ L (logCutoff A t) (box (A:=A) (d:=d) (H:=H) (Y:=Y) b (rowWidth j b))≤
      (C/(L:ℝ)+1/((j:ℝ)+1))*((b:ℝ)*rowWidth j b)
  have rows (j : ℕ) : ∀ᶠ b in atTop,pred j b := by
    by_cases enough : J≤j
    case neg => exact Eventually.of_forall (fun _ h=>False.elim (enough h))
    obtain ⟨t₀,h⟩:=eventually_atTop.mp (middle j enough)
    refine eventually_atTop.mpr ⟨2^(400*t₀)+1,?_⟩
    intro b hb _ t eq
    have ht : t₀≤t := by
      by_contra! ne
      have le:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_left 400 ne.le)
      rw [eq,length_pow] at hb;omega
    exact eq ▸ h t ht
  obtain ⟨s,up,good,grow,short⟩:=choose_width ω pred slow rows
  let w := fun b=>rowWidth (s b) b
  let boxes : CountingBoxes A d H Y:=numericalBoxes w (fun m=>eventually_atTop.mp (tendsto_atTop.mp grow m))
    (fun ε ep=>eventually_atTop.mp (short ε ep))
  have count : CountsAt A d H Y T κ K L boxes σ := counts w grow short (good.mono (fun b h=>h.2))
  have near := (relative_error A).eventually_lt_const (by linarith : 0<σ/16)
  have eps := (eventual_error up (by linarith : 0<σ/16))
  have total := (main_eventually count sig big kl inT inAux).and ((eventually_area_pos boxes).and (eps.and good))
  have stages:=(up.eventually (eventually_ge_atTop J))
  have all := (length_grows.eventually (total.and stages)).and (near.and ((tendsto_atTop.mp (cutoff_grows A) L).and (cutoff_within A)))
  obtain ⟨t,bounds⟩:=all.exists
  let N:=lengthAt t
  let W:=w N
  obtain ⟨⟨⟨main,ar,error,mid,_⟩,stage⟩,small,lr,within⟩:=bounds
  have wid : W≤ side t := (Nat.div_le_self _ _).trans_eq (Nat.sqrt_eq' _)
  have large:=log_tail (A:=A) (d:=d) (H:=H) (Y:=Y) T κ t W wid (by omega) within (fun p hp=>(inT p hp).trans (kl.trans lr)) (fun p hp=>(inAux p hp).trans (kl.trans lr))
  let S:=box (A:=A) (d:=d) (H:=H) (Y:=Y) N W
  let X:ℝ:=(N:ℝ)*W
  have hi : removedMass T κ (logCutoff A t) S ≤(meanConstant A/(growthBound A t:ℝ))*X := large
  have md : middleMass T κ L (logCutoff A t) S ≤(C/(L:ℝ)+1/((s N:ℝ)+1))*X := mid stage t rfl
  change 0<X at ar
  change σ/4*X≤ mainMass T κ L S at main
  refine ⟨S,?_⟩
  change removedMass T κ L S < mainMass T κ L S
  rw [split_removed _ _ _ _ lr _]
  apply (add_le_add md hi).trans_lt
  apply lt_of_lt_of_le _ main
  rw [←add_mul];apply mul_lt_mul_of_pos_right _ ar
  change 1/((s N:ℝ)+1)≤σ/16 at error
  linarith

end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.log_surplus
