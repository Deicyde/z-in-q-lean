import LocalSymbols
import ZInQKernel.RouteK.Slots.Symbols

namespace Sun28.FixedLocalRows
open ZInQ.RouteK

/-- The F₂ label of a Boolean squareclass character. -/
def parity (b : Bool) : ZMod 2 := if b then 1 else 0

theorem parity_xor (a b : Bool) : parity (a ^^ b) = parity a + parity b := by
  cases a <;> cases b <;> decide
theorem parity_and (a b : Bool) : parity (a && b) = parity a * parity b := by
  cases a <;> cases b <;> decide

theorem parity_symbol (p : ℕ) [Fact p.Prime] (a : ℤ) :
    parity (symbol p a) = legBit p a := by
  classical
  have eq := @legBit_eq_one_iff p _ a
  rw [jacobiSym.legendreSym.to_jacobiSym] at eq
  rcases legBit_eq_zero_or_one p a with hz | hu
  · have ne : jacobiSym a p ≠ -1 := fun h => (by decide : (0:ZMod 2)≠1) (hz.symm.trans (eq.mpr h))
    simp [symbol,parity,ne,hz]
  · simp [symbol,parity,eq.mp hu,hu]

/-- Linear evaluation of a table of unit characters on the selected generators. -/
def total : List (ZMod 2) → Nat → Word → ZMod 2
  | [], _, _ => 0
  | c :: cs, i, v => c * parity (v.getLsbD i) + total cs (i+1) v

private theorem parity_accum (cs : List Bool) (i : Nat) (v : Word) (b : Bool) :
    parity (accumulate cs i v b) = parity b + total (cs.map parity) i v := by
  induction cs generalizing i b with
  | nil => simp [accumulate,total]
  | cons c cs ih =>
    simp only [accumulate,List.map_cons,total,ih,parity_xor]
    cases c <;> simp [parity,add_assoc]

theorem parity_dot (cs : List Bool) (i : Nat) (v : Word) :
    parity (bitDot cs i v) = total (cs.map parity) i v := by
  change parity (accumulate cs i v false) = _
  rw [parity_accum]
  exact zero_add _

theorem total_append (as bs : List (ZMod 2)) (i : Nat) (v : Word) :
    total (as ++ bs) i v = total as i v + total bs (i+as.length) v := by
  induction as generalizing i with
  | nil => simp [total]
  | cons a as ih =>
    simp only [List.cons_append,total,ih,List.length_cons,add_assoc, Nat.add_comm 1 as.length]

theorem total_add {α : Type*} (g h : α → ZMod 2) (s : List α) (i : Nat) (v : Word) :
    total (s.map (fun t=>g t+h t)) i v = total (s.map g) i v + total (s.map h) i v := by
  induction s generalizing i with
  | nil => simp [total]
  | cons a as ih => simp [total,ih,add_mul];ring

theorem total_scale {α : Type*} (g : α → ZMod 2) (k : ZMod 2) (s : List α) (i : Nat) (v : Word) :
    total (s.map (fun t=>g t*k)) i v = total (s.map g) i v*k := by
  induction s generalizing i with
  | nil => simp [total]
  | cons a as ih => simp [total,ih,add_mul];ring

/-- The Legendre bit of a selected product of p-adic units is the dot product
of the Legendre bits of the generators with the exponent bits. -/
theorem unit_character {p : ℕ} [Fact p.Prime] (s : List ℤ) (i : Nat) (v : Word)
    (units : ∀ a∈s, ¬ (p:ℤ)∣a) :
    ¬(p:ℤ)∣generatorProduct s i v ∧
    legBit p (generatorProduct s i v) = total (s.map (legBit p)) i v := by
  have prime := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have nz {a:ℤ} (h:¬(p:ℤ)∣a) : (a:ZMod p)≠0 := by rwa [ne_eq,ZMod.intCast_zmod_eq_zero_iff_dvd]
  have notOne : ¬(p:ℤ)∣1 := fun h => prime.not_isUnit (isUnit_of_dvd_one h)
  have bitOne : legBit p 1 = 0 := by simp [legBit]
  induction s generalizing i with
  | nil => simpa [generatorProduct,total] using And.intro notOne bitOne
  | cons a s ih =>
    have au := units a (by simp)
    obtain ⟨un,bit⟩ := ih (i+1) (fun r z=>units r (by simp [z]))
    cases val : v.getLsbD i with
    | false => simpa [generatorProduct,val,total,parity] using And.intro un bit
    | true =>
      have live := fun h => (prime.dvd_or_dvd h).elim au un
      simpa [generatorProduct,val,total,parity,legBit_mul (nz au) (nz un),bit] using
        And.intro (show ¬ (p:ℤ) ∣ a * generatorProduct s (i+1) v from live)
          (legBit_mul (nz au) (nz un))

end Sun28.FixedLocalRows
#print axioms Sun28.FixedLocalRows.parity_symbol
#print axioms Sun28.FixedLocalRows.parity_dot
#print axioms Sun28.FixedLocalRows.unit_character
