import FieldNormal
namespace PhysicalProjection.FieldRows.Sparse
open ZeroInput.Sparse ProjectionDescent

private def insertSlot (i : Nat) : List Nat→List Nat
  | []=>[i] | j::js=>if i≤j then i::j::js else j::insertSlot i js
private def sortSlots : List Nat→List Nat | []=>[] | i::is=>insertSlot i (sortSlots is)
private theorem slot_insert (z : Assignment) (i : Nat) (m : List Nat) : monomialValue z (insertSlot i m)=z i*monomialValue z m := by
  induction m with | nil => rfl | cons j js ih =>
    unfold insertSlot;split <;> simp only [monomialValue,ih] <;> grobner
private theorem slot_sort (z : Assignment) (m : List Nat) : monomialValue z (sortSlots m)=monomialValue z m := by
  induction m with | nil=>rfl | cons j js ih=>simp only [sortSlots,slot_insert,monomialValue,ih]
private theorem slot_append (z : Assignment) (a b : List Nat) : monomialValue z (a++b)=monomialValue z a*monomialValue z b := by
  induction a with | nil=>simp [monomialValue] | cons j js ih=>simp only [List.cons_append,monomialValue,ih];grobner

def cp (n : Int) : Polynomial := [⟨n,[]⟩]
def vp (i : Nat) : Polynomial := [⟨1,[i]⟩]
def ap (a b : Polynomial) := a++b
abbrev sp := ProjectionDescent.scale
private def pt (a b : Term) : Term := ⟨a.coefficient*b.coefficient,a.monomial++b.monomial⟩
def mp (a b : Polynomial) := a.flatMap (fun t => b.map (pt t))
@[simp] theorem at_c (x : Assignment) (n : Int) : value x (cp n)=(n:Rat) := by simp [cp,value,termValue,monomialValue,Rat.add_zero]
@[simp] theorem at_v (x : Assignment) (i : Nat) : value x (vp i)=x i := by simp [vp,value,termValue,monomialValue,Rat.add_zero]
@[simp] theorem at_a (x : Assignment) (a b : Polynomial) : value x (ap a b)=value x a+value x b := value_append ..
@[simp] theorem at_s (x : Assignment) (n : Int) (a : Polynomial) : value x (sp n a)=(n:Rat)*value x a := scale_value ..
@[simp] theorem at_m (x : Assignment) (a b : Polynomial) : value x (mp a b)=value x a*value x b := by
  have one (t : Term) (l : Polynomial) : value x (l.map (pt t))=termValue x t*value x l := by
    induction l with | nil=>simp [value] | cons h l ih=>simp only [List.map_cons,value,ih,pt,termValue,slot_append,Rat.intCast_mul];grobner
  induction a with | nil=>simp [mp,value] | cons h a ih=>change value x (b.map (pt h)++mp a b)=_;rw [value_append,one,ih];simp only [value];grobner

private def push (t : Term) : Polynomial→Polynomial
  | []=>[t] | h::hs=>if t.monomial=h.monomial then ⟨t.coefficient+h.coefficient,h.monomial⟩::hs else h::push t hs
private def reduce : Polynomial→Polynomial | []=>[] | t::ts=>push ⟨t.coefficient,sortSlots t.monomial⟩ (reduce ts)
private theorem push_value (x : Assignment) (t : Term) (p : Polynomial) : value x (push t p)=termValue x t+value x p := by
  induction p with
  | nil=>rfl
  | cons h p ih =>
    unfold push;split <;> rename_i eq
    · simp only [value,termValue,Rat.intCast_add,eq];grobner
    · simp only [value,ih];grobner
private theorem reduce_value (x : Assignment) (p : Polynomial) : value x (reduce p)=value x p := by
  induction p with | nil=>rfl | cons t ts ih=>simp only [value,reduce,push_value,ih,termValue,slot_sort]

def cert (a b : Polynomial) := (reduce (ap a (sp (-1) b))).all (fun t=>t.coefficient==0)
theorem sound {a b : Polynomial} (h : cert a b=true) (x : Assignment) : value x a=value x b := by
  have z (p : Polynomial) (zero : p.all (fun t=>t.coefficient==0)=true) : value x p=0 := by
    induction p with | nil=>rfl | cons t ts ih=> have spl : t.coefficient=0 ∧ ts.all (fun t=>t.coefficient==0)=true := by simpa using zero
                                                 simp [value,termValue,spl.1,ih spl.2,Rat.add_zero]
  have eq:=z _ h
  rw [reduce_value,at_a,at_s] at eq;grobner
end PhysicalProjection.FieldRows.Sparse
