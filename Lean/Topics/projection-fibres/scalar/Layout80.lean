import ScalarRows
import PhysicalLocality

namespace ProjectionFibres.Actual
open StructuralReduction.Transfer84

abbrev Base := Fin 78→Rat
abbrev Index := Sum (Fin 78) (Fin 6)

/-- The 78 fixed slots retain their original order. The final six positions are
the two reciprocal coordinates, the three recovered scalars and the inverse. -/
def decode (i : Fin 84) : Index :=
  match i.val with
  | 20 => .inr 0 | 21 => .inr 1 | 28 => .inr 2 | 26 => .inr 3
  | 27 => .inr 4 | 83 => .inr 5
  | n => .inl ⟨(if n<20 then n else if n<26 then n-2 else n-5)%78,by omega⟩

def encode : Index→Fin 84
  | .inl j => ⟨if j.val<20 then j.val else if j.val<24 then j.val+2 else j.val+5,by split <;> first | omega | split <;> omega⟩
  | .inr j => match j.val with
    | 0=>20 | 1=>21 | 2=>28 | 3=>26 | 4=>27 | _=>83

theorem roundtrip : ∀ i : Fin 84,encode (decode i)=i := by decide +kernel

def six (a b d m v g : Rat) (j : Fin 6) : Rat :=
  match j.val with
  | 0=>a | 1=>b | 2=>d | 3=>m | 4=>v | _=>g

def assign (B : Base) (v : Fin 6→Rat) (j : Fin 84) := (decode j).elim B v

def fill (B : Base) (a b d m v g : Rat) := assign B (six a b d m v g)

theorem decompose (x : Fin 84→Rat) :
    ∃ B a b d m v g,x=fill B a b d m v g := by
  let B : Base := fun k=>x (encode (.inl k))
  let Q : Fin 6→Rat := fun k=>x (encode (.inr k))
  have eta : six (Q 0) (Q 1) (Q 2) (Q 3) (Q 4) (Q 5)=Q := by
    funext k
    have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
    rcases hc with h|h|h|h|h|h <;> subst k <;> rfl
  refine ⟨B,Q 0,Q 1,Q 2,Q 3,Q 4,Q 5,?_⟩
  unfold fill
  rw [eta]
  funext k
  change x k=(decode k).elim B Q
  have back:=roundtrip k
  cases h : decode k with
  | inl j => rw [h] at back;exact congrArg x back.symm
  | inr j => rw [h] at back;exact congrArg x back.symm

def extraClass (j : Fin 6) := if j.val<2 then 1 else 2

private theorem layoutClass : ∀ j : Fin 84,slotClass (j.val+1)=
    (decode j).elim (fun _=>0) extraClass := by decide +kernel

theorem agreement (B : Base) (u v : Fin 6→Rat) (k : Nat)
    (agree : ∀ j,extraClass j≤k → u j=v j) :
    ∀ i,slotClass i≤k → cell (assign B u) i=cell (assign B v) i := by
  intro i h
  unfold cell
  split
  · rename_i b
    let j : Fin 84 := ⟨i-1,by omega⟩
    have eq : j.val+1=i := by dsimp [j];omega
    have shape:=layoutClass j
    rw [eq] at shape
    change (decode j).elim B u=(decode j).elim B v
    rw [shape] at h
    cases a : decode j with
    | inl i => rfl
    | inr k => apply agree;simpa [a] using h
  · rfl

def empty (B : Base) := fill B 0 0 0 0 0 0

def fixed (B : Base) (i : Nat) := wire (empty B) i

theorem base_guard (B : Base) (a b d m v g : Rat) :
    wire (fill B a b d m v g) 9915 = fixed B 9915 :=
  same_wire 0 (agreement B _ _ 0 (by intro j z;unfold extraClass at z;split at z <;> omega))
    (by decide) (by decide +kernel)

def retained : List Nat := [984,782,677,489,463,459,455,451,
  1304,1428,1552,1676,1800,4100,4149,4273,4397,4521,4645,6910,
  6959,7083,7207,7331,7455,9720]

private theorem levels : retained.all (fun j=>decide (j<9918 ∧ level j≤1))=true := by decide +kernel

theorem retained_agree (B : Base) (a b d m v g : Rat) {j : Nat} (hj : j∈retained) :
    wire (fill B a b d m v g) j=wire (fill B a b 0 0 0 0) j := by
  obtain ⟨bound,dep⟩:= of_decide_eq_true (List.all_eq_true.mp levels j hj)
  apply same_wire 1 (agreement B _ _ 1 ?_) bound dep
  intro k cond
  unfold extraClass at cond
  split at cond
  · rename_i lt
    have : k=0 ∨ k=1 := by omega
    rcases this with h|h <;> subst k <;> rfl
  · omega

end ProjectionFibres.Actual
