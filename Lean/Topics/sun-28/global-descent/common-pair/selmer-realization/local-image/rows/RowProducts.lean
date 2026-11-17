import WordCharacters

namespace Sun28.FixedLocalRows
open ZInQ.RouteK

def generators : List ℤ := [-1,2,3,11,109,439,283,1433,4373,14557]
def badPrimes : List ℕ := [11,109,439,283,1433,4373,14557]
def fixedN : ℤ := 13588380161692636619

def orderBit (p : ℕ) (i : ℕ) (v : Word) : ZMod 2 :=
  total (generators.map fun a => parity (decide (a=(p:ℤ)))) i v

def unitPart (p : ℕ) (i : ℕ) (v : Word) : ℤ :=
  generatorProduct (generators.map (unitFactor p)) i v

private theorem dot_map {α : Type*} (f : α→Bool) (s : List α) (i : Nat) (v : Word) :
    total ((s.map f).map parity) i v = total (s.map (fun a=>parity (f a))) i v := by
  simp [List.map_map,Function.comp_def]

theorem prime_units (p : ℕ) (hp : p∈3::badPrimes) :
    ∀ a∈generators.map (unitFactor p), ¬ (p:ℤ)∣a := by
  simp [badPrimes] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

private theorem char_product (p : ℕ) [Fact p.Prime] (hp : p∈3::badPrimes) (i : Nat) (v : Word) :
    total (generators.map (fun a=>legBit p (unitFactor p a))) i v = legBit p (unitPart p i v) := by
  have h := (unit_character (generators.map (unitFactor p)) i v (prime_units p hp)).2
  simpa [unitPart,List.map_map,Function.comp_def] using h.symm

theorem row_value_a (p : ℕ) [Fact p.Prime] (hp : p∈badPrimes) (v : Word) :
    parity (bitDot (localRow p false) 0 v) =
    legBit p (unitPart p 0 v) + orderBit p 0 v * legBit p (fixedN/p) +
      orderBit p 10 v * legBit p 3 := by
  change parity (bitDot ((generators.map fun (a:ℤ) =>
      symbol p (unitFactor p a) ^^ (decide (a=(p:ℤ)) && symbol p (fixedN/p))) ++
      (generators.map fun (b:ℤ) => decide (b=(p:ℤ)) && symbol p 3)) 0 v) = _
  rw [parity_dot,List.map_append,total_append,dot_map,dot_map]
  simp only [parity_xor,parity_and,parity_symbol]
  rw [total_add,total_scale,total_scale,char_product p (List.mem_cons_of_mem 3 hp)]
  rfl

theorem row_value_b (p : ℕ) [Fact p.Prime] (hp : p∈badPrimes) (v : Word) :
    parity (bitDot (localRow p true) 0 v) =
    legBit p (unitPart p 10 v) + orderBit p 10 v * legBit p (-(fixedN/p)) := by
  change parity (bitDot ((generators.map fun (_:ℤ) => false) ++
      (generators.map fun (b:ℤ) => symbol p (unitFactor p b) ^^
               (decide (b=(p:ℤ)) && symbol p (-(fixedN/p))))) 0 v) = _
  rw [parity_dot,List.map_append,total_append,dot_map,dot_map]
  simp only [parity_xor,parity_and,parity_symbol]
  rw [total_add,total_scale,char_product p (List.mem_cons_of_mem 3 hp)]
  have zeroPart : total (generators.map (fun _ => parity false)) 0 v=0 := by
    simp [generators,total,parity]
  rw [zeroPart,zero_add]
  rfl

theorem row_three (v : Word) :
    parity (bitDot threeUnits 0 v) = legBit 3 (unitPart 3 10 v) := by
  change parity (bitDot (List.replicate 10 false ++
    generators.map (fun b=>symbol 3 (unitFactor 3 b))) 0 v) = _
  rw [parity_dot,List.map_append,total_append,dot_map]
  simp only [parity_symbol]
  rw [char_product 3 (by simp)]
  have zz (k i : ℕ) : total (List.replicate k 0) i v=0 := by
    induction k generalizing i with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,total,ih]
  have z : total (List.map parity (List.replicate 10 false)) 0 v = 0 := zz 10 0
  rw [z,zero_add]
  rfl

end Sun28.FixedLocalRows
#print axioms Sun28.FixedLocalRows.prime_units
#print axioms Sun28.FixedLocalRows.row_value_a
#print axioms Sun28.FixedLocalRows.row_value_b
#print axioms Sun28.FixedLocalRows.row_three
