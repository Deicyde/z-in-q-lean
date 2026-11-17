import SupportMatrix
import Mathlib.Data.Matrix.Reflection

namespace Sun28.SupportMatrix
open Matrix

/-- Least significant bit gives the first support prime. -/
def bits {k : ℕ} (row : ℕ) (j : Fin k) : F := if row.testBit j.val then 1 else 0
def rows {k : ℕ} (r : Fin k → ℕ) : Matrix (Fin k) (Fin k) F := fun i => bits (r i)

def small : Matrix (Fin 4) (Fin 4) F := rows ![6,3,0,5]
def large : Matrix (Fin 5) (Fin 5) F := rows ![6,3,0,29,24]

def smallCertificate : Certificate small (bits 13) (bits 12) (bits 9) (bits 7) (bits 8) :=
  { inverse := rows ![4,6,7,0]
    constants := by decide
    marked := by decide
    odd_sign := by decide
    selector_total := by decide
    selector_mark := by decide
    reciprocity := by decide
    left_product := by decide
    right_product := by decide }

def largeCertificate : Certificate large (bits 13) (bits 12) (bits 9) (bits 7) (bits 8) :=
  { inverse := rows ![4,6,7,0,16]
    constants := by decide
    marked := by decide
    odd_sign := by decide
    selector_total := by decide
    selector_mark := by decide
    reciprocity := by decide
    left_product := by decide
    right_product := by decide }

end Sun28.SupportMatrix
#print axioms Sun28.SupportMatrix.smallCertificate
#print axioms Sun28.SupportMatrix.largeCertificate
