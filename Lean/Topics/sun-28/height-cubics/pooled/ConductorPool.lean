import TameChart

namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres Refinement
noncomputable section

/-- Product of the contributions of row i in its three possible roles. -/
def rowWeight (i:Fin 5) (A B:ℤ) :=
  primeProduct (baseSet i A B)*(primeProduct (squareSet i A B))^2*(primeProduct (cubeSet i A B))^2

def weight (A B:ℤ) := ∏ i:Fin 5,rowWeight i A B

private theorem rotate_one (f:Fin 5→ℕ) : (∏ i:Fin 5,f (i+1))=∏ i:Fin 5,f i := by
  simp only [Fin.prod_univ_succ]
  change f 1*(f 2*(f 3*(f 4*(f 0*1))))=f 0*(f 1*(f 2*(f 3*(f 4*1))))
  ring

private theorem rotate_two (f:Fin 5→ℕ) : (∏ i:Fin 5,f (i+2))=∏ i:Fin 5,f i := by
  simp only [Fin.prod_univ_succ]
  change f 2*(f 3*(f 4*(f 0*(f 1*1))))=f 0*(f 1*(f 2*(f 3*(f 4*1))))
  ring

theorem cyclic_product (A B:ℤ) : (∏ i:Fin 5,cap (cycle i) A B)=exceptional^5*weight A B := by
  let d (i:Fin 5):=primeProduct (baseSet i A B)
  let g (i:Fin 5):=(primeProduct (squareSet i A B))^2
  let h (i:Fin 5):=(primeProduct (cubeSet i A B))^2
  change (∏ i:Fin 5,exceptional*d i*g (i+2)*h (i+1))=exceptional^5*∏ i:Fin 5,d i*g i*h i
  simp only [Finset.prod_mul_distrib,rotate_one,rotate_two,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

def ChartTest (A B:ℤ) : Prop := ∃ r:ThreeRows,heightBound (cap r A B)≤glazerConstant24*(oddProduct A B:ℝ)^24

theorem five_height_of_chart (pub:PublishedElliptic) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (h:ChartTest A B) : target A B := by
  obtain ⟨r,cmp⟩:=h
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using (height_of_chart pub r cop off).trans cmp

theorem chart_of_small {A B:ℤ} (r:ThreeRows) (small:cap r A B≤62208*heightRadical A B^23) :
    ChartTest A B := by
  have p:0<heightRadical A B:=Nat.mul_pos pos_cutoff (pos_odd _ _)
  have c:=absorb_cap (cap_pos r A B) p small
  have m:(2:ℝ)^31≤2^810:=pow_le_pow_right₀ (by norm_num) (by decide)
  exact ⟨r,(c.trans (mul_le_mul_of_nonneg_right m (by positivity))).trans (original_margin A B)⟩

/-- Five cyclic charts suffice for the same geometric mean as all 60 orderings. -/
theorem chart_of_product {A B:ℤ} (budget:1225^5*weight A B≤heightRadical A B^115) :
    ChartTest A B := by
  let T:=heightRadical A B
  have pos:0<T:=Nat.mul_pos pos_cutoff (pos_odd _ _)
  by_contra fail
  have large (i:Fin 5):62208*T^23<cap (cycle i) A B:=
    lt_of_not_ge (fun s=>fail (chart_of_small _ s))
  have strict:(∏ _i:Fin 5,62208*T^23)<∏ i:Fin 5,cap (cycle i) A B:=
    Finset.prod_lt_prod_of_nonempty₀ (fun _ _=>by positivity) (fun i _=>large i) Finset.univ_nonempty
  have left:(∏ _i:Fin 5,62208*T^23)=62208^5*T^115:=by simp [mul_pow,←pow_mul]
  rw [left,cyclic_product,show exceptional=62208*1225 by decide,mul_pow,mul_assoc] at strict
  exact (not_lt_of_ge (Nat.mul_le_mul_left (62208^5) budget)) strict

theorem failure_weight {A B:ℤ} (bad:¬ChartTest A B) :
    heightRadical A B^115 < 1225^5*weight A B := lt_of_not_ge (fun h=>bad (chart_of_product h))

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.cyclic_product
#print axioms Sun28.HeightCubics.Pooled.five_height_of_chart
#print axioms Sun28.HeightCubics.Pooled.chart_of_small
#print axioms Sun28.HeightCubics.Pooled.chart_of_product
#print axioms Sun28.HeightCubics.Pooled.failure_weight
