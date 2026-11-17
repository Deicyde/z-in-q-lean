import PrimeRectangles

namespace Sun28.SinglePrime
open Finset Filter Topology Sun28.MixedSieve Sun28.WeightedSelection
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

def area (boxes : CountingBoxes A d H Y) (b : ℕ) : ℝ := (b:ℝ)*(boxes.width b:ℝ)

theorem eventually_area_pos (boxes : CountingBoxes A d H Y) :
    ∀ᶠ b in atTop,0<area boxes b := by
  obtain ⟨m,hm⟩:=boxes.grows 1
  filter_upwards [eventually_ge_atTop m,eventually_ge_atTop (1:ℕ)] with b hb hb'
  apply mul_pos
  · exact_mod_cast hb'
  · exact_mod_cast hm b hb

/-- The ordinary prime pattern in the base ray, and three individual ray tests at each new prime.
All the statements for this cutoff use the same width. -/
structure CountsAt (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ K L : ℕ)
    (boxes : CountingBoxes A d H Y) (σ : ℝ) : Prop where
  base : Tendsto (fun b=>baseCount (boxes.records b) T κ K/area boxes b) atTop (𝓝 σ)
  single : ∀ p∈places K L, ∀ j : Test,
    Tendsto (fun b=>rectCount (boxes.records b) T κ K p j/area boxes b) atTop
      (𝓝 (σ*localProportion A p j))

theorem bad_limit {T : Finset ℕ} {κ K L : ℕ} {boxes : CountingBoxes A d H Y} {σ : ℝ}
    (counts : CountsAt A d H Y T κ K L boxes σ) (kp : 2810≤K)
    (inT : ∀ p∈T,p≤K) (inAux : ∀ p∈κ.primeFactors,p≤K) {p : ℕ} (hp : p∈places K L) :
    Tendsto (fun b=>badCount (boxes.records b) T κ K p/area boxes b) atTop (𝓝 (σ*markedLoss A p)) := by
  obtain ⟨gt,_,prime⟩:=mem_places.mp hp
  have iden (b : ℕ) := bad_count (boxes.records b) T κ K p prime (by omega)
    (fun h=> (not_le_of_gt gt) (inT _ h)) (fun h=> (not_le_of_gt gt) (inAux _ h))
  have sums := ((counts.base.sub (counts.single p hp .plus)).sub
    (counts.single p hp .minus)).add (counts.single p hp .both)
  have h:=signed_local A p prime (by omega)
  have e : σ-σ*localProportion A p .plus-σ*localProportion A p .minus+
      σ*localProportion A p .both=σ*markedLoss A p := by linear_combination -σ*h
  rw [←e]
  simpa only [iden,add_div,sub_div] using sums

/-- For any fixed cutoff the same positive fraction of the ordinary base density survives. -/
theorem main_eventually {T : Finset ℕ} {κ K L : ℕ} {boxes : CountingBoxes A d H Y} {σ : ℝ}
    (counts : CountsAt A d H Y T κ K L boxes σ) (pos : 0<σ) (kp : 2810≤K) (kl : K≤L)
    (inT : ∀ p∈T,p≤K) (inAux : ∀ p∈κ.primeFactors,p≤K) :
    ∀ᶠ b in atTop,(σ/4)*area boxes b≤ mainMass T κ L (boxes.records b) := by
  let P:=places K L
  have total:=tendsto_finsetSum P (fun p hp=>bad_limit counts kp inT inAux hp)
  have sub:=counts.base.sub total
  have loss := marked_large_sum A P fun p hp=>by have h:= (mem_places.mp hp).1;omega
  have mag : σ/4<σ-∑p∈P,σ*markedLoss A p := by
    rw [←Finset.mul_sum]
    nlinarith only [pos,mul_le_mul_of_nonneg_left loss pos.le]
  have near:=sub.eventually_const_lt mag
  filter_upwards [near,eventually_area_pos boxes] with b good xp
  change σ/4 < baseCount (boxes.records b) T κ K/area boxes b-
    ∑ p∈P,badCount (boxes.records b) T κ K p/area boxes b at good
  rw [←Finset.sum_div,←sub_div] at good
  exact ((lt_div_iff₀ xp).mp good).le.trans (finite_lower _ _ _ _ _ kl (by omega))

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.eventually_area_pos
#print axioms Sun28.SinglePrime.bad_limit
#print axioms Sun28.SinglePrime.main_eventually
