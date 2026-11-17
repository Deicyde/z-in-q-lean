import FieldS10
import FieldS11
import FieldS710
import FieldS711
import FieldA
import FieldT
import FieldZ
import FieldS708
import FieldS709
import FieldS712
import FieldS713
import FieldS714
import FieldS715
import FieldS188
import FieldS189
import FieldS209
import FieldS210
import FieldS148
import FieldS149
namespace PhysicalProjection.FieldRows
open ZeroInput.Sparse ProjectionDescent Triangular.Data

theorem component_identity (g : Bool) (k : Block) (r : Relation) (im : Bool) (x : Assignment) : value x (literal g k r im)=rowScale k r im*component im (formula g k r x) := by
  cases k <;> cases r <;> cases im
  · exact literal2 g x
  · exact literal3 g x
  · exact literal700 g x
  · exact literal701 g x
  · exact literal702 g x
  · exact literal703 g x
  · exact literal704 g x
  · exact literal705 g x
  · exact literal706 g x
  · exact literal707 g x
  · exact literal184 g x
  · exact literal185 g x
  · exact literal207 g x
  · exact literal208 g x
  · exact literal142 g x
  · exact literal143 g x
  · exact literal10 g x
  · exact literal11 g x
  · exact literal708 g x
  · exact literal709 g x
  · exact literal710 g x
  · exact literal711 g x
  · exact literal712 g x
  · exact literal713 g x
  · exact literal714 g x
  · exact literal715 g x
  · exact literal188 g x
  · exact literal189 g x
  · exact literal209 g x
  · exact literal210 g x
  · exact literal148 g x
  · exact literal149 g x
  · exact literal18 g x
  · exact literal19 g x
  · exact literal716 g x
  · exact literal717 g x
  · exact literal718 g x
  · exact literal719 g x
  · exact literal720 g x
  · exact literal721 g x
  · exact literal722 g x
  · exact literal723 g x
  · exact literal192 g x
  · exact literal193 g x
  · exact literal211 g x
  · exact literal212 g x
  · exact literal160 g x
  · exact literal161 g x
  · exact literal26 g x
  · exact literal27 g x
  · exact literal724 g x
  · exact literal725 g x
  · exact literal726 g x
  · exact literal727 g x
  · exact literal728 g x
  · exact literal729 g x
  · exact literal730 g x
  · exact literal731 g x
  · exact literal196 g x
  · exact literal197 g x
  · exact literal213 g x
  · exact literal214 g x
  · exact literal172 g x
  · exact literal173 g x
theorem literal_is_parent_row (g : Bool) (k : Block) (r : Relation) (im : Bool) : (number k r im,literal g k r im)∈top::rest g := by
  cases k <;> cases r <;> cases im
  · exact List.mem_of_getElem? (show (top::rest g)[1]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[2]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[91]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[92]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[93]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[94]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[95]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[96]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[97]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[98]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[31]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[32]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[39]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[40]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[15]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[16]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[3]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[4]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[99]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[100]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[101]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[102]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[103]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[104]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[105]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[106]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[33]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[34]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[41]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[42]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[19]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[20]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[5]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[6]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[107]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[108]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[109]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[110]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[111]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[112]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[113]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[114]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[35]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[36]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[43]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[44]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[23]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[24]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[7]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[8]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[115]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[116]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[117]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[118]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[119]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[120]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[121]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[122]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[37]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[38]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[45]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[46]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[27]?=some _ by cases g <;> rfl)
  · exact List.mem_of_getElem? (show (top::rest g)[28]?=some _ by cases g <;> rfl)
theorem nonzero_scale (k : Block) (r : Relation) (im : Bool) : rowScale k r im≠0 := by cases k <;> cases r <;> cases im <;> simp only [rowScale] <;> grobner
theorem paired_rows_iff (g : Bool) (k : Block) (r : Relation) (x : Assignment) :
    (value x (literal g k r false)=0 ∧ value x (literal g k r true)=0) ↔ formula g k r x=(0,0) := by
  rw [component_identity,component_identity]
  constructor
  · rintro ⟨a,b⟩
    exact Prod.ext ((Rat.mul_eq_zero.mp a).resolve_left (nonzero_scale k r false)) ((Rat.mul_eq_zero.mp b).resolve_left (nonzero_scale k r true))
  · intro eq;rw [eq];simp [component]

#print axioms Sparse.sound
#print axioms Sparse.branches_zero
#print axioms paired_rows_iff
#print axioms shifted_S
#print axioms shifted_a
#print axioms shifted_b
#print axioms inflate_value
#print axioms component_identity
#print axioms literal_is_parent_row
#print axioms nonzero_scale
end PhysicalProjection.FieldRows
