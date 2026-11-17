import GoodMarked
import FamilyLocal

namespace Sun28.SeededPartners
open Sun28.SelmerRealization Sun28.PairedClasses Sun28.PreparedPoles
open ZInQ.RouteK.Selmer
open private find_parameter from GoodMarked

/-- For a fixed mark b, its complementary multiplier is l/b. -/
theorem square_chart {K : Type*} [Field K] [CharZero K] {b q : ℕ}
    (h : IsSquare (b:K) ∨ IsSquare (q:K)) : Cover K (b*q) b 1 := by
  rcases h with ⟨r,R⟩|⟨r,R⟩
  · refine ⟨1,r,1,0,Or.inl one_ne_zero,?_,?_⟩ <;> push_cast <;> rw [R] <;> ring
  · refine ⟨r,0,2*r,1,Or.inr (Or.inr (Or.inr one_ne_zero)),?_,?_⟩ <;>
      push_cast <;> rw [R] <;> ring

theorem lift_unit {p m : ℕ} [Fact p.Prime] (p2 : p≠2) (u : ¬p∣m)
    (s : IsSquare (m:ZMod p)) : IsSquare (m:ℚ_[p]) := by
  have h := isSquare_intCast_of_residue (p:=p) (c:=(m:ℤ)) p2
    (by exact_mod_cast u) (by simpa only [Int.cast_natCast] using s)
  simpa only [Int.cast_natCast] using h

theorem residue_of_local_square {p m : ℕ} [Fact p.Prime] (h : LocalSquareAt p m) :
    IsSquare (m:ZMod p) := by
  obtain ⟨t,ht⟩ := h 1
  rw [pow_one] at ht
  have eq := (ZMod.intCast_eq_intCast_iff (t^2) (m:ℤ) p).mpr ht
  push_cast at eq
  exact ⟨t,by linear_combination -eq⟩

/-- Away from 6bq every prime admits a point, even when neither unit is a square. -/
theorem good_place {p b q : ℕ} [Fact p.Prime] (large : 3<p) (bu : ¬p∣b) (qu : ¬p∣q) :
    Cover ℚ_[p] (b*q) b 1 := by
  have odd : p≠2 := by omega
  by_cases hb : IsSquare (b:ZMod p)
  · exact square_chart (Or.inl (lift_unit odd bu hb))
  by_cases hq : IsSquare (q:ZMod p)
  · exact square_chart (Or.inr (lift_unit odd qu hq))
  obtain ⟨t,tn,unit,square⟩ := find_parameter p large q b hq hb
  let T : ℤ := t.val
  have lift : (T:ZMod p)=t := by simp [T]
  let A : ℤ := b*(T^2-q)*(T^2-9*q)
  have residue : (A:ZMod p)=(b:ZMod p)*(t^2-q)*(t^2-9*q) := by push_cast [A];rw [lift]
  have Au : ¬(p:ℤ)∣A := by
    intro d
    exact unit (residue.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr d))
  obtain ⟨s,S⟩ := isSquare_intCast_of_residue odd Au (residue.symm ▸ square)
  have Tn : (T:ℚ_[p])≠0 := by
    have nz : T≠0 := fun H => tn (lift.symm.trans (by rw [H,Int.cast_zero]))
    exact_mod_cast nz
  let U : ℚ_[p] := (T^2-3*q)/(2*T)
  let V : ℚ_[p] := (T^2+3*q)/(2*T)
  have bound : (b:ℚ_[p])*(T^2-q)*(T^2-9*q)=s*s := by simpa [A] using S
  refine ⟨U,s/(2*T),V,1,Or.inr (Or.inr (Or.inr one_ne_zero)),?_,?_⟩
  · push_cast; dsimp [U]; field_simp [Tn];linear_combination bound
  · push_cast; dsimp [U,V]; field_simp [Tn];ring

end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.square_chart
#print axioms Sun28.SeededPartners.residue_of_local_square
#print axioms Sun28.SeededPartners.good_place
