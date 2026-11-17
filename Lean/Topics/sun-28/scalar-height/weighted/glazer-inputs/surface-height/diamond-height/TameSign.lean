import ScalarCochain

namespace ZInQBlueprint.DiamondHeight
noncomputable section

/-- A single odd multiplier removes the odd part at every small prime.
The number e below is at least the binary logarithm of the cutoff. -/
theorem odd_multiplier (S:Finset ℕ) (e:ℕ) (small:∀p∈S,p.Prime ∧ p≤2^e) :
    ∃ k:ℕ, Odd k ∧ ∀p∈S, p-1 ∣ k*2^e := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by decide,by simp⟩
  | @insert p s outside ih =>
    obtain ⟨k,odd,all⟩:=ih (fun q hq=>small q (Finset.mem_insert_of_mem hq))
    obtain ⟨prime,cap⟩:=small p (Finset.mem_insert_self ..)
    obtain ⟨v,u,ou,eqn⟩:=Nat.exists_eq_two_pow_mul_odd (n:=p-1) (by have :=prime.two_le;omega)
    have dp : 2^v ∣ p-1 := ⟨u,eqn⟩
    have vp : 2^v≤2^e := (Nat.le_of_dvd (by have :=prime.two_le;omega) dp).trans ((Nat.sub_le ..).trans cap)
    have ve : v≤e := (pow_le_pow_iff_right₀ (by decide : (1:ℕ)<2)).mp vp
    refine ⟨u*k,ou.mul odd,?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl|h
    · rw [eqn]
      obtain ⟨z,hz⟩:=pow_dvd_pow 2 ve
      exact ⟨k*z, by rw [hz];ring⟩
    · exact (all q h).trans ⟨u,by ring⟩

variable {G Q K:Type*} [Group G] [Group Q] [CommGroup K] {q:G →* Q}

/-- Odd powers preserve the same sign cocycle. -/
def InflatedSplitting.oddPower (F:InflatedSplitting (K:=K) q)
    (sign : ∀ x y,(F.factor x y)^2=1) {k:ℕ} (odd:Odd k) : InflatedSplitting (K:=K) q where
  b x := (F.b x)^k
  factor := F.factor
  left_one := F.left_one
  right_one := F.right_one
  split x y := by
    rw [←mul_pow,F.split,mul_pow]
    obtain ⟨v,h⟩:=odd
    rw [h,pow_succ,pow_mul,sign,one_pow,one_mul]

/-- If k=2h+1 then the new splitting differs by the global character χ^h. -/
theorem odd_power_ratio (F:InflatedSplitting (K:=K) q) (χ:G →* K)
    (square:∀g,(F.b g)^2=χ g) (h:ℕ) (g:G) :
    (F.b g)^(2*h+1)/F.b g=(χ g)^h := by
  rw [pow_succ,pow_mul,square,mul_div_cancel_right]

/-- The scalar multiplying the Tate action uses the inverse of the new cochain. -/
theorem inverse_odd_power (F:InflatedSplitting (K:=K) q) (χ:G →* K)
    (square:∀g,(F.b g)^2=χ g) (h:ℕ) (g:G) :
    ((F.b g)^(2*h+1))⁻¹=((χ g)^h)⁻¹*(F.b g)⁻¹ := by
  rw [pow_succ,pow_mul,square,mul_inv_rev,mul_comm]

/-- Orders at large primes remain paired with their Euler factors. -/
def largeUnitOrders (S : Finset ℕ) := ∏ p∈S,(p-1)

theorem bounded_character_orders (S O : Finset ℕ) (e:ℕ) (dyadic:0<e)
    (small:∀p∈S,p.Prime ∧ p≤2^e) (large:∀p∈O,p.Prime) :
    ∃ k:ℕ, Odd k ∧ ∀ (δ:G →* K) ( _dy:∀g,(δ g)^2=1)
      (ι : ∀p:ℕ,G →* (ZMod p)ˣ) (χ:∀p:ℕ,(ZMod p)ˣ →* K) (g:G),
      ((δ g * (∏p∈S,χ p (ι p g)) * ∏p∈O,χ p (ι p g))^k)^(2^e*largeUnitOrders O)=1 := by
  obtain ⟨k,odd,kill⟩:=odd_multiplier S e small
  refine ⟨k,odd,?_⟩
  intro δ dy ι χ g
  let m:=2^e*largeUnitOrders O
  have d2 : 2∣k*m := (show 2∣2^e from (by simpa only [pow_one] using (pow_dvd_pow 2 dyadic : (2:ℕ)^1∣2^e))).trans
    (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  have ord (p:ℕ) (pr:p.Prime) (dvd:p-1∣k*m) : (χ p (ι p g))^(k*m)=1 := by
    let : NeZero p:=⟨pr.ne_zero⟩
    obtain ⟨a,ha⟩:=dvd
    rw [ha,pow_mul,←map_pow,←Nat.totient_prime pr,←ZMod.card_units_eq_totient,pow_card_eq_one,map_one,one_pow]
  change (_^k)^m=1
  rw [←pow_mul,mul_pow,mul_pow,←Finset.prod_pow,←Finset.prod_pow]
  have dd : (δ g)^(k*m)=1 :=
    (orderOf_dvd_iff_pow_eq_one).mp ((orderOf_dvd_of_pow_eq_one (dy g)).trans d2)
  have ds : ∀p∈S,χ p (ι p g)^(k*m)=1:=fun p h=>ord p (small p h).1
    ((kill p h).trans ⟨largeUnitOrders O,by dsimp [m];ring⟩)
  have dl : ∀p∈O,χ p (ι p g)^(k*m)=1:=fun p h=>ord p (large p h)
    ((show p-1 ∣ largeUnitOrders O from Finset.dvd_prod_of_mem (fun p:ℕ => p-1) h).trans ⟨k*2^e,by dsimp only [m];ac_rfl⟩)
  rw [dd,Finset.prod_eq_one ds,Finset.prod_eq_one dl,one_mul,one_mul]

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.odd_multiplier
#print axioms ZInQBlueprint.DiamondHeight.InflatedSplitting.oddPower
#print axioms ZInQBlueprint.DiamondHeight.odd_power_ratio
#print axioms ZInQBlueprint.DiamondHeight.inverse_odd_power
#print axioms ZInQBlueprint.DiamondHeight.bounded_character_orders
