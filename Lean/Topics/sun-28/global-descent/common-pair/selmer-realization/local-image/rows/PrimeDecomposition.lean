import WordFactors
import RowProducts

namespace Sun28.FixedLocalRows

/-- The p-position of the fixed list is the single exponent represented by the dot product. -/
theorem singleton_order {p : ℕ} (hp : p∈3::badPrimes) (v : Word) (i : Nat) :
    ∃ j : Nat, generators[j]?=some (p:ℤ) ∧
      orderBit p i v = parity (v.getLsbD (i+j)) ∧
      generators.map (unitFactor p)=generators.map (fun a => if a=(p:ℤ) then 1 else a) := by
  simp [badPrimes] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | refine ⟨2,by decide,?_,by decide⟩
    | refine ⟨3,by decide,?_,by decide⟩
    | refine ⟨4,by decide,?_,by decide⟩
    | refine ⟨5,by decide,?_,by decide⟩
    | refine ⟨6,by decide,?_,by decide⟩
    | refine ⟨7,by decide,?_,by decide⟩
    | refine ⟨8,by decide,?_,by decide⟩
    | refine ⟨9,by decide,?_,by decide⟩
  all_goals simp [orderBit,generators,total,parity,List.map,Nat.add_assoc]

theorem decomposition {p : ℕ} (hp : p∈3::badPrimes) (v : Word) (i : Nat) :
    ∃ x : Nat, x<2 ∧ generatorProduct generators i v =
    (p:ℤ)^x * unitPart p i v ∧ (x:ZMod 2) = orderBit p i v := by
  obtain ⟨j,pos,ord,remove⟩ := singleton_order hp v i
  refine ⟨(v.getLsbD (i+j)).toNat,?_,?_,?_⟩
  · cases v.getLsbD (i+j) <;> decide
  · rw [unitPart,remove]
    exact insert_factor (p:ℤ) generators j i v (by decide) pos
  · rw [ord]
    cases v.getLsbD (i+j) <;> decide

end Sun28.FixedLocalRows
#print axioms Sun28.FixedLocalRows.singleton_order
#print axioms Sun28.FixedLocalRows.decomposition
