import CharacterTable

namespace Sun28.SelmerRealization
open Matrix Sun28.SupportMatrix
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def seven : Fin 7 → ℕ := ![11,109,439,283,1433,4373,14557]

def fixedMatrix : Matrix (Fin 7) (Fin 7) F := rows ![46,43,0,126,24,75,40]

def firstCertificate :
    Certificate fixedMatrix (bits 13) (bits 60) (bits 9) (bits 7) (bits 8) :=
  { inverse := rows ![4,70,7,0,20,64,102]
    constants := by decide
    marked := by decide
    odd_sign := by decide
    selector_total := by decide
    selector_mark := by decide
    reciprocity := by decide
    left_product := by decide
    right_product := by decide }

theorem exact_symbols : ArithmeticTable seven fixedMatrix (bits 13) (bits 60) := by
  refine ⟨?_, ?_, ?_, firstCertificate.constants⟩
  · intro i; fin_cases i <;> norm_num [seven]
  · intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [fixedMatrix, rows, bits, symbolBit, seven] <;> decide
  · intro i; fin_cases i <;> norm_num [bits, symbolBit, seven] <;> decide

theorem first_support_solutions (u v : Vec (Fin 7)) (δ : F) :
    (fixedMatrix *ᵥ u + diagonal (bits 60) *ᵥ v = δ • bits 60 ∧
      (fixedMatrix + diagonal (bits 13)) *ᵥ v = 0 ∧
      ((bits 60 : Vec (Fin 7)) + bits 13) ⬝ᵥ v = 0) ↔
    v = 0 ∧ δ = 0 ∧ ∃ c d : F, u = c • 1 + d • bits 7 :=
  rows_iff firstCertificate

end Sun28.SelmerRealization
#print axioms Sun28.SelmerRealization.firstCertificate
#print axioms Sun28.SelmerRealization.exact_symbols
#print axioms Sun28.SelmerRealization.first_support_solutions
