import SelectedMatrices
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.FinCases

namespace Sun28.SupportMatrix
open Matrix
def support4 : Fin 4 → ℕ := ![11,109,439,331]
def support5 : Fin 5 → ℕ := ![11,109,439,331,526681]
def symbolBit (a : ℤ) (p : ℕ) : F := if jacobiSym a p = -1 then 1 else 0

def ArithmeticTable {k : ℕ} (p : Fin k → ℕ) (K : Matrix (Fin k) (Fin k) F)
    (s l : Vec (Fin k)) : Prop :=
  (∀ i, (p i).Prime) ∧ (∀ i j, i ≠ j → K i j = symbolBit (p j) (p i)) ∧
  (∀ i, s i = symbolBit (-1) (p i) ∧ l i = symbolBit 3 (p i)) ∧ K *ᵥ 1 = 0

theorem small_symbols : ArithmeticTable support4 small (bits 13) (bits 12) := by
  refine ⟨?_, ?_, ?_, smallCertificate.constants⟩
  · intro i; fin_cases i <;> norm_num [support4]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [small, rows, bits, symbolBit, support4] <;> decide
  · intro i; fin_cases i <;> norm_num [bits, symbolBit, support4] <;> decide

theorem large_symbols : ArithmeticTable support5 large (bits 13) (bits 12) := by
  refine ⟨?_, ?_, ?_, largeCertificate.constants⟩
  · intro i; fin_cases i <;> norm_num [support5]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [large, rows, bits, symbolBit, support5] <;> decide
  · intro i; fin_cases i <;> norm_num [bits, symbolBit, support5] <;> decide

end Sun28.SupportMatrix
#print axioms Sun28.SupportMatrix.small_symbols
#print axioms Sun28.SupportMatrix.large_symbols
