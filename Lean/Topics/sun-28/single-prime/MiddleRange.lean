import LargeWindow

namespace Sun28.SinglePrime
open Sun28.ContactFactors Sun28.WeightedSelection Sun28.ContactSieve Filter Topology
open scoped Classical
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

def middleMass (T : Finset ℕ) (κ L R : ℕ) (S : Finset (Record A d H Y)) : ℝ :=
  ∑ a∈S.filter (fun a=>below a T κ L ∧ ¬below a T κ R),weight a

theorem split_removed (T : Finset ℕ) (κ L R : ℕ) (lr : L≤R) (S : Finset (Record A d H Y)) :
    removedMass T κ L S=middleMass T κ L R S + removedMass T κ R S := by
  simp only [middleMass,removedMass,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have small : below a T κ R → below a T κ L :=
    fun h p hp odd seven low=>h p hp odd seven (low.trans lr)
  have tail' : below a T κ R → (tail a T κ L ↔ tail a T κ R) := by
    intro all
    constructor
    · rintro ⟨p,pp,odd,seven,gt,fail⟩
      exact ⟨p,pp,odd,seven,lt_of_not_ge (fun le=>fail (all p pp odd seven le)),fail⟩
    · rintro ⟨p,pp,odd,seven,gt,fail⟩; exact ⟨p,pp,odd,seven,lr.trans_lt gt,fail⟩
  by_cases h : below a T κ R
  · by_cases t : tail a T κ R <;> simp [h,small h,tail' h,t]
  · have m : below a T κ L → tail a T κ L := by
      intro lo
      by_contra miss
      apply h
      intro p pp odd seven pr
      by_cases pl : p≤L
      · exact lo p pp odd seven pl
      · by_contra bad;exact miss ⟨p,pp,odd,seven,by omega,bad⟩
    by_cases low : below a T κ L <;> simp_all

theorem length_grows : Tendsto lengthAt atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [eventually_ge_atTop j] with t ht
  rw [length_pow]
  exact (by omega : j≤400*t).trans (Nat.lt_pow_self (by decide : 1<2)).le

theorem split_grows : Tendsto splitAt atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [eventually_ge_atTop j] with t ht
  exact (by omega : j≤2*t).trans (Nat.lt_pow_self (by decide : 1<2)).le

/-- Only the primes strictly above L and at most the moving dyadic threshold remain.
The row index is fixed before the height tends to infinity. -/
def MiddleRow (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ L : ℕ) (C : ℝ) : Prop :=
  ∀ j : ℕ,∀ᶠ t : ℕ in atTop,
    let N:=lengthAt t
    let W:=rowWidth j N
    middleMass T κ L (splitAt t) (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W)≤
      (C/(L:ℝ)+1/((j:ℝ)+1))*((N:ℝ)*W)

theorem middle_surplus {T : Finset ℕ} {κ K L : ℕ} {σ C : ℝ} (base : CountThreshold A d H Y T κ K L σ)
    (middle : MiddleRow A d H Y T κ L C) (big : 2810≤K) (kl : K≤L)
    (inT : ∀ p∈T,p≤K) (inAux : ∀ p∈κ.primeFactors,p≤K) (sig : 0<σ) (margin : C/(L:ℝ)<σ/8) :
    ∃ S : Finset (Record A d H Y),surplus T κ L S := by
  obtain ⟨ω,slow,counts⟩:=base
  let pred := fun j b=>∀ t : ℕ,b=lengthAt t →
    middleMass T κ L (splitAt t) (box (A:=A) (d:=d) (H:=H) (Y:=Y) b (rowWidth j b))≤
      (C/(L:ℝ)+1/((j:ℝ)+1))*((b:ℝ)*rowWidth j b)
  have rows (j : ℕ) : ∀ᶠ b in atTop,pred j b := by
    obtain ⟨t₀,h⟩:=eventually_atTop.mp (middle j)
    refine eventually_atTop.mpr ⟨2^(400*t₀)+1,?_⟩
    intro b hb t eq
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
  have near := (error_tendsto A).eventually_lt_const (by linarith : 0<σ/16)
  have eps := (eventual_error up (by linarith : 0<σ/16))
  have total := (main_eventually count sig big kl inT inAux).and ((eventually_area_pos boxes).and (eps.and good))
  have all := (length_grows.eventually total).and (near.and ((tendsto_atTop.mp split_grows L).and (eventually_ge_atTop (1:ℕ))))
  obtain ⟨t,bounds⟩:=all.exists
  let N:=lengthAt t
  let W:=w N
  obtain ⟨⟨main,ar,error,mid,_⟩,small,lr,tp⟩:=bounds
  have wid : W≤ side t := (Nat.div_le_self _ _).trans_eq (Nat.sqrt_eq' _)
  have large:=large_window (A:=A) (d:=d) (H:=H) (Y:=Y) T κ t W tp wid (fun p hp=>(inT p hp).trans (kl.trans lr)) (fun p hp=>(inAux p hp).trans (kl.trans lr))
  let S:=box (A:=A) (d:=d) (H:=H) (Y:=Y) N W
  let X:ℝ:=(N:ℝ)*W
  have hi : removedMass T κ (splitAt t) S ≤errorFactor A t*X := large
  have md : middleMass T κ L (splitAt t) S ≤(C/(L:ℝ)+1/((s N:ℝ)+1))*X := mid t rfl
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
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.split_removed
#print axioms Sun28.SinglePrime.middle_surplus
