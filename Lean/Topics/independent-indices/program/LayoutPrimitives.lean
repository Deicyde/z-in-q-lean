import IndexLayout

namespace IndependentIndices
open CircuitTransport Data
set_option maxRecDepth 20000

def vector {n : Nat} (x : Fin n→Rat) (i : Nat) : Rat :=
  if hi : 0<i ∧ i≤n then x ⟨i-1,by omega⟩ else 0

def parentAt (i : Nat) : Nat :=
  if 0<i ∧ i≤134 then parentLookup i else 0

def diagonal (x : Fin 74→Rat) (i : Fin 134) : Rat := vector x (parentAt (i.val+1))

theorem diagonal_at (x : Fin 74→Rat) (i : Nat) :
    vector (diagonal x) i=vector x (parentAt i) := by
  by_cases hi : 0<i ∧ i≤134
  · simp only [vector,dif_pos hi,diagonal]
    rw [show i-1+1=i by omega]
  · simp [vector,hi,parentAt]

theorem first_input (x : Fin 74→Rat) : vector (diagonal x) 1=vector x 1 := by
  rw [diagonal_at,show parentAt 1=1 by decide +kernel]

def srcRef (r : Ref) : Ref := ⟨(newRoutes[r.cell]!).family,r.node,r.origin⟩

def correctRoute (k : Nat) : Bool :=
  let c:=newRoutes[k]!
  let old:=oldRoutes[c.family]!
  decide (old.family=c.family ∧ old.slots.toList=c.slots.toList.map parentAt)

def inFrame (f : Frame) (i : Nat) : Bool :=
  decide (1≤i ∧ i≤17) || match f with
  | .common => false
  | .first => decide (18≤i ∧ i≤52)
  | .second => decide (53≤i ∧ i≤87)
  | .third => decide (88≤i ∧ i≤122)
  | .scalar => decide (123≤i ∧ i≤134)

def routeOK (k : Nat) : Bool :=
  let c:=newRoutes[k]!
  correctRoute k && c.slots.toList.all (inFrame c.frame)

def covers (t s : List Ref) : Bool := t.all (fun r=>s.any (fun q=>decide (srcRef r=q))) &&
    s.all (fun r=>t.any (fun q=>decide (srcRef q=r)))


/-- Check a single supplied pair of addresses by inspecting the two actual references. -/
def matchesAt (t s : List Ref) (i j : Nat) : Bool :=
  match t[i]?,s[j]? with
  | some q,some r => decide (srcRef q=r)
  | _,_ => false

def ForwardAt (t s : List Ref) (i : Nat) : Prop :=
  ∀ q,t[i]?=some q → ∃r∈s,srcRef q=r

def BackAt (t s : List Ref) (j : Nat) : Prop :=
  ∀ r,s[j]?=some r → ∃q∈t,srcRef q=r

theorem match_forward (t s : List Ref) (i j : Nat) (ok : matchesAt t s i j=true) :
    ForwardAt t s i := by
  intro q h
  unfold matchesAt at ok
  rw [h] at ok
  cases hs : s[j]? with
  | none => simp [hs] at ok
  | some r =>
    exact ⟨r,List.mem_of_getElem? hs,of_decide_eq_true (by simpa only [hs] using ok)⟩

theorem match_back (t s : List Ref) (i j : Nat) (ok : matchesAt t s i j=true) :
    BackAt t s j := by
  intro r h
  unfold matchesAt at ok
  rw [h] at ok
  cases ht : t[i]? with
  | none => simp [ht] at ok
  | some q =>
    exact ⟨q,List.mem_of_getElem? ht,of_decide_eq_true (by simpa only [ht] using ok)⟩

def Between (P : Nat→Prop) (lo hi : Nat) : Prop := ∀i,lo≤i → i<hi → P i

theorem at_one {P : Nat→Prop} {i : Nat} (h : P i) : Between P i (i+1) := by
  intro j lo hi
  have eq : j=i := by omega
  exact eq ▸ h

theorem join_at {P : Nat→Prop} {lo mid hi : Nat} (a : Between P lo mid) (b : Between P mid hi) :
    Between P lo hi := by
  intro j h1 h2
  by_cases left : j<mid
  · exact a j h1 left
  · exact b j (by omega) h2

theorem covers_by_addresses (t s : List Ref) (f : Between (ForwardAt t s) 0 t.length)
    (b : Between (BackAt t s) 0 s.length) : covers t s=true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro q hq
    obtain ⟨i,hi,eq⟩:=List.getElem_of_mem hq
    obtain ⟨r,hr,e⟩:=f i (Nat.zero_le _) hi q (by rw [List.getElem?_eq_getElem hi,eq])
    exact List.any_eq_true.mpr ⟨r,hr,decide_eq_true e⟩
  · apply List.all_eq_true.mpr
    intro r hr
    obtain ⟨i,hi,eq⟩:=List.getElem_of_mem hr
    obtain ⟨q,hq,e⟩:=b i (Nat.zero_le _) hi r (by rw [List.getElem?_eq_getElem hi,eq])
    exact List.any_eq_true.mpr ⟨q,hq,decide_eq_true e⟩

end IndependentIndices
