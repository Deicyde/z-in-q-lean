import Projection80
import InputRestriction

namespace ProjectionFibres.Actual
open StructuralReduction StructuralReduction.Transfer84 InputRestriction

def reflect (x : Fin 84→Rat) (i : Fin 84) : Rat := if i.val=0 then -1-x i else x i
theorem reflected_first (x : Fin 84→Rat) : cell (reflect x) 1= -1-cell x 1 := rfl

private theorem reflected_agree (x : Fin 84→Rat) : ∀ k,distinguished k≤0 →
    cell (reflect x) k=cell x k := by
  intro k ok
  unfold distinguished at ok
  split at ok
  · omega
  · rename_i outside
    unfold cell
    split
    · rename_i bound
      simp [reflect,show k-1≠0 by omega]
    · rfl

private theorem reflected_square (x : Fin 84→Rat) :
    childWire archiveAt (reflect x) 91=childWire archiveAt x 91 := by
  rw [input_square,input_square,reflected_first];grobner

theorem reflected_ordinary (x : Fin 84→Rat) : output false (reflect x)=0 ↔ output false x=0 := by
  have safe : Output.wireList.all (fun j=>decide (j<9918 ∧ sensitive j≤0))=true := by decide +kernel
  have each {j : Nat} (m : j∈Output.wireList) :
      childWire archiveAt (reflect x) j=childWire archiveAt x j := by
    obtain ⟨bound,lvl⟩:=of_decide_eq_true (List.all_eq_true.mp safe _ m)
    exact same_except_square (reflected_agree x) (reflected_square x) bound lvl
  rw [show (output false (reflect x)=0) ↔ _ from (signed84 archiveAt _).1,
      show (output false x=0) ↔ _ from (signed84 archiveAt _).1]
  constructor <;> intro good j m
  · exact (each m).symm.trans (good j m)
  · exact (each m).trans (good j m)

def Image (mark : Bool) (T : Rat) := ∃ y : Fin 80→Rat,y 0=T ∧ output80 mark y=0

private theorem forward (T : Rat) (h : Image false T) : Image false (-1-T) := by
  obtain ⟨x,i,z⟩:=(projection_iff false T).mpr h
  exact (projection_iff false _).mp ⟨reflect x,by rw [reflected_first,i],(reflected_ordinary x).mpr z⟩

theorem mirror_image (T : Rat) : Image false T ↔ Image false (-1-T) := by
  refine ⟨forward T,?_⟩
  intro h
  have back:=forward _ h
  rwa [show -1-(-1-T)=T by grobner] at back

theorem marked_image (T : Rat) : Image true T ↔ T=0 ∨ Image false T := by
  constructor
  · rintro ⟨x,i,z⟩
    change x 0*ordinary80 x=0 at z
    exact (Rat.mul_eq_zero.mp z).elim (fun h=>Or.inl (i.symm.trans h)) (fun h=>Or.inr ⟨x,i,h⟩)
  · rintro (rfl|⟨x,i,h⟩)
    · exact ⟨fun _=>0,rfl,Rat.zero_mul _⟩
    · exact ⟨x,i,by change x 0*ordinary80 x=0;change ordinary80 x=0 at h;rw [h,Rat.mul_zero]⟩

private theorem integer_reflect {T : Rat} (h : IsInteger T) : IsInteger (-1-T) := by
  obtain ⟨n,rfl⟩:=h
  exact ⟨-1-n,by rw [Rat.intCast_sub];rfl⟩

/-- Nonnegative integers suffice for existence and half the rational line for soundness. -/
def HalfTheorem : Prop :=
  (∀ n : Nat, Image false (n:Rat)) ∧ (∀ T : Rat,0≤2*T+1 → Image false T → IsInteger T)

theorem ordinary_iff_half : (∀T,Image false T ↔ IsInteger T) ↔ HalfTheorem := by
  constructor
  · intro h
    exact ⟨fun n=>(h _).mpr ⟨(n:Int),rfl⟩,fun T _ x=>(h T).mp x⟩
  · rintro ⟨atNat,sound⟩ T
    constructor
    · intro x
      by_cases side : 0≤2*T+1
      · exact sound T side x
      · have right : 0≤2*(-1-T)+1 := by grind
        have h:=integer_reflect (sound _ right ((mirror_image T).mp x))
        rwa [show -1-(-1-T)=T by grobner] at h
    · rintro ⟨n,rfl⟩
      cases n with
      | ofNat i => exact atNat i
      | negSucc i =>
        have z : ((Int.negSucc i:Int):Rat)= -1-(i:Rat) := by
          change ((-((i:Int)+1):Int):Rat)=_
          rw [Rat.intCast_neg,Rat.intCast_add,Rat.intCast_natCast];grobner
        rw [z];exact (mirror_image _).mp (atNat i)

/-- An ordinary zero above −1 reflects to an ordinary zero at 0. -/
theorem marked_iff_ordinary :
    (∀T,Image true T ↔ IsInteger T) ↔ ∀T,Image false T ↔ IsInteger T := by
  constructor
  · intro h T
    constructor
    · intro z;exact (h T).mp ((marked_image T).mpr (Or.inr z))
    · intro z
      by_cases eq : T=0
      · subst T
        have neg : Image true (-1) := (h _).mpr ⟨-1,rfl⟩
        have ordinary:=((marked_image _).mp neg).resolve_left (by decide)
        have back:=(mirror_image (-1)).mp ordinary
        rwa [show (-1-(-1):Rat)=0 by grobner] at back
      · exact ((marked_image T).mp ((h T).mpr z)).resolve_left eq
  · intro h T
    rw [marked_image,h]
    exact ⟨fun z=>z.elim (fun eq=>⟨0,eq⟩) id,Or.inr⟩

theorem defining_iff_half (mark : Bool) : (∀ T,Image mark T ↔ IsInteger T) ↔ HalfTheorem := by
  cases mark with
  | false=>exact ordinary_iff_half
  | true=>exact marked_iff_ordinary.trans ordinary_iff_half

#print axioms mirror_image
#print axioms marked_iff_ordinary
#print axioms defining_iff_half
end ProjectionFibres.Actual
