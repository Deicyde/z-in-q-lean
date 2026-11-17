import ChartSupport
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 12000
set_option maxHeartbeats 600000

def DBlock.rows : DBlock→Rows
  | .one=>[(304,p304),(521,p521),(544,p544),(545,p545),(546,p546),(526,p526)]
  | .two=>[(354,p354),(528,p528),(550,p550),(551,p551),(552,p552),(533,p533)]
  | .three=>[(404,p404),(535,p535),(556,p556),(557,p557),(558,p558),(540,p540)]

def PPair.rows (k : PPair) : Rows := [(k.rid,k.f),(k.rid+1,k.g)]

def DBlock.atPoint (k : DBlock) (z : Assignment) : Prop :=
  let e:=z k.e; let a:=z (k.e+1); let b:=z (k.e+2); let c:=z (k.e+3); let d:=z (k.e+4)
  let q:=z (k.e+5); let Q:=z (k.e+6); let t:=k.t z
  e*(1+a*t^3)=0 ∧ e*b=a^2 ∧ e*a*c=b^2 ∧ c*d=(e*a)^5 ∧ c*q=d^2 ∧ c*Q=q^4

theorem detector_rows (g : Bool) (k : DBlock) (z : Assignment) (ok : ∀p∈ps g,p.ok z) :
    rowsHold k.rows z ↔ k.atPoint z := by
  cases k
  case one =>
    have cub := ok p314 (List.mem_of_getElem? (show (ps g)[11]?=some p314 by cases g <;> rfl))
    simp [Pivot.ok,Pivot.num,p314,scale,value,termValue,monomialValue] at cub
    simp [rowsHold,DBlock.rows,DBlock.atPoint,DBlock.e,DBlock.t,p304,p521,p544,p545,p546,p526,value,termValue,monomialValue]
    constructor <;> rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ <;> exact ⟨by grobner,by grobner,by grobner,by grobner,by grobner,by grobner⟩
  case two =>
    have cub := ok p364 (List.mem_of_getElem? (show (ps g)[39]?=some p364 by cases g <;> rfl))
    simp [Pivot.ok,Pivot.num,p364,scale,value,termValue,monomialValue] at cub
    simp [rowsHold,DBlock.rows,DBlock.atPoint,DBlock.e,DBlock.t,p354,p528,p550,p551,p552,p533,value,termValue,monomialValue]
    constructor <;> rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ <;> exact ⟨by grobner,by grobner,by grobner,by grobner,by grobner,by grobner⟩
  case three =>
    have cub := ok p414 (List.mem_of_getElem? (show (ps g)[56]?=some p414 by cases g <;> rfl))
    simp [Pivot.ok,Pivot.num,p414,scale,value,termValue,monomialValue] at cub
    simp [rowsHold,DBlock.rows,DBlock.atPoint,DBlock.e,DBlock.t,p404,p535,p556,p557,p558,p540,value,termValue,monomialValue]
    constructor <;> rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ <;> exact ⟨by grobner,by grobner,by grobner,by grobner,by grobner,by grobner⟩

theorem detector_original {k : DBlock} {z : Assignment} (ok : k.atPoint z) :
    CircuitTransport.Detector.Original (z k.e) (k.t z) (z (k.e+1)) (z (k.e+5)) (z (k.e+6)) :=
  ⟨z (k.e+2),z (k.e+3),z (k.e+4),ok⟩

private def removedRows := detectors.flatMap DBlock.rows ++ pairs.flatMap PPair.rows

theorem split_rows (g : Bool) (z : Assignment) : rowsHold (top::rest g) z ↔
    rowsHold (activeRows g) z ∧ (∀k : DBlock, rowsHold k.rows z) ∧ (∀k : PPair, rowsHold k.rows z) := by
  let f : (Nat×Polynomial)→Bool := fun r => (detIds++pairIds).contains r.1
  let order : List Nat := [0, 6, 12, 1, 5, 7, 11, 13, 17, 2, 3, 4, 8, 9, 10, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25]
  let permuted := order.filterMap fun i => removedRows[i]?
  have ordered : (top::rest g).filter f = permuted := by cases g <;> rfl
  have known : ∀ i : Fin 26, i.val∈order := by decide
  have same {r : Nat×Polynomial} : r∈permuted ↔ r∈removedRows := by
    constructor
    · intro h; obtain ⟨i,_,v⟩:=List.mem_filterMap.mp h; exact List.mem_of_getElem? v
    · intro h; obtain ⟨i,idx⟩:=List.getElem?_of_mem h
      have len:= (List.getElem?_eq_some_iff.mp idx).1
      have bound : i<26 := len
      exact List.mem_filterMap.mpr ⟨i,known ⟨i,bound⟩,idx⟩

  have cat (all : rowsHold removedRows z) : (∀k : DBlock, rowsHold k.rows z) ∧ (∀k : PPair, rowsHold k.rows z) := by
    constructor
    · intro k r hr; apply all r; apply List.mem_append_left; apply List.mem_flatMap.mpr
      exact ⟨k,by cases k <;> decide,hr⟩
    · intro k r hr; apply all r; apply List.mem_append_right; apply List.mem_flatMap.mpr
      exact ⟨k,by cases k <;> decide,hr⟩
  constructor
  · intro h
    refine ⟨fun r hr => h r (List.mem_filter.mp hr).1,cat ?_⟩
    intro r hr; have sorted : r∈permuted := same.mpr hr
    rw [←ordered] at sorted; exact h r (List.mem_filter.mp sorted).1
  · rintro ⟨act,ds,qs⟩ r hr
    by_cases removed : f r=true
    · have rmem : r∈(top::rest g).filter f := List.mem_filter.mpr ⟨hr,removed⟩
      rw [ordered] at rmem
      rcases List.mem_append.mp (same.mp rmem) with left|right
      · obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp left; exact ds k r hk
      · obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp right; exact qs k r hk
    · exact act r (List.mem_filter.mpr ⟨hr,by change (!(f r))=true;simpa using removed⟩)

end PhysicalProjection
