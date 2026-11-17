import Clear
namespace CircuitTransport

def select (base : Coords) (a : Array (Option Cell)) (i : Nat) : Cell :=
  match a[i]? with | some (some c) => c | _ => base i

def fill (b : Book) (base : Coords) : List Triangular.Pivot → Array (Option Cell) → Array (Option Cell)
  | [], a => a
  | p::ps,a =>
    let c := pivotCell b (select base a) p
    fill b base ps (a.setIfInBounds p.slot (some c))

private def largest : List Triangular.Pivot → Nat
  | [] => 0
  | p::ps => max p.slot (largest ps)

private theorem largest_bound (ps : List Triangular.Pivot) : ∀ p∈ps, p.slot≤largest ps := by
  induction ps with
  | nil => simp
  | cons h ps ih =>
    intro p hp;rcases List.mem_cons.mp hp with e|m
    · subst p; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih p m) (Nat.le_max_right _ _)

def cells (b : Book) (ps : List Triangular.Pivot) (base : Coords) : Array (Option Cell) :=
  fill b base ps (Array.replicate (largest ps+1) none)

def memo (b : Book) (ps : List Triangular.Pivot) (base : Coords) : Coords :=
  select base (cells b ps base)

private theorem select_set (base : Coords) (a : Array (Option Cell)) (j : Nat) (c : Cell)
    (bound : j<a.size) : select base (a.setIfInBounds j (some c))=update (select base a) j c := by
  funext i;by_cases h : i=j
  · subst i;simp [select,update,Array.getElem?_setIfInBounds_self_of_lt bound]
  · simp [select,update,h,Ne.symm h]

private theorem fill_eq (b : Book) (base : Coords) (ps : List Triangular.Pivot)
    (a : Array (Option Cell)) (bound : ∀ p∈ps, p.slot<a.size) :
    select base (fill b base ps a)=restore b ps (select base a) := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    let c := pivotCell b (select base a) p
    change select base (fill b base ps (a.setIfInBounds p.slot (some c)))=_
    have tail : ∀ q∈ps, q.slot<(a.setIfInBounds p.slot (some c)).size :=
      fun q mem => by simpa using bound q (List.mem_cons_of_mem _ mem)
    rw [ih _ tail,select_set _ _ _ _ (bound p (by simp))];rfl

theorem memo_eq (b : Book) (ps : List Triangular.Pivot) (base : Coords) : memo b ps base=restore b ps base := by
  let a : Array (Option Cell) := Array.replicate (largest ps+1) none
  have bound : ∀ p∈ps, p.slot<a.size := fun p mem => by
    have le := largest_bound ps p mem; simp [a];omega
  have init : select base a=base := by
    funext i; unfold select; rw [show a[i]? = (if i<largest ps+1 then some none else none) from Array.getElem?_replicate]
    by_cases h : i<largest ps+1 <;> simp [h]
  change select base (fill b base ps a)=_
  rw [fill_eq _ _ _ _ bound,init]

end CircuitTransport
