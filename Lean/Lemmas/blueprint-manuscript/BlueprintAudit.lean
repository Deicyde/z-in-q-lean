import LiteralV15
import ManuscriptArithmetic

open ManuscriptV15

/-- This is an executable check of the bound input text, independent of the Python serializer. -/
private def shape {n : ℕ} (rows : List (Row n)) : ℕ × ℕ × ℕ :=
  (rows.length, rows.foldl (fun d r => max d r.slots.length) 0,
    rows.foldl (fun d r => max d r.parameterPower) 0)

#eval (parseRows 314 fixedText).map shape
#eval (parseRows 222 familyText).map shape
#print axioms ManuscriptV15.padding_projection
#print axioms ManuscriptV15.fixed314_to_frozen
#print axioms ManuscriptV15.defining_member_above
#print axioms ManuscriptV15.Arithmetic.mem_contact_iff
#print axioms ManuscriptV15.Arithmetic.infinity_contributes
