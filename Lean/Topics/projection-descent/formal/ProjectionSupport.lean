import ProjectionCore

namespace ProjectionDescent
open ZeroInput.Sparse

theorem substitute_absent (j : Nat) (c : Int) (num p : Polynomial) (h : width j p=0) :
    substitute j c num p=p := by simp [substitute,h]

def checkRows (I : List Nat) (f : Family) (live : Nat→Bool) : Bool := I.all fun i => reads live (f i)
theorem checked_support {I f live} (h : checkRows I f live=true) : ∀ i∈I, supported live (f i) := by
  intro i mem; exact reads_supported (List.all_eq_true.mp h i mem)

def overlay (x : Assignment) : List (Nat×Rat) → Assignment
  | [] => x
  | hd::rest => put (overlay x rest) hd.1 hd.2

def off (priv : List Nat) (x y : Assignment) : Prop := ∀ i, i∉priv → y i=x i

theorem overlay_off (x : Assignment) (entries : List (Nat×Rat)) :
    off (entries.map Prod.fst) x (overlay x entries) := by
  intro i outside
  induction entries with
  | nil => rfl
  | cons hd es ih =>
    have split : i≠hd.1 ∧ i∉es.map Prod.fst := by simpa using outside
    change put (overlay x es) hd.1 hd.2 i=x i
    simp [put,split.1,ih split.2]

def apart (priv : List Nat) (i : Nat) : Bool := !priv.contains i

theorem agree_off {priv x y} (away : off priv x y) (p : Polynomial) (sf : supported (apart priv) p) :
    value y p=value x p := by
  apply sf; intro i ok
  exact away i (by simpa [apart] using ok)

theorem remove_mem {i k : Nat} {I : List Nat} : k∈removeId i I ↔ k∈I ∧ k≠i := by
  simp [removeId]

/-- Replace the three disjoint physical equations by one, preserving each outside coordinate. -/
theorem pole_project (I : List Nat) (f : Family) (a m z : Nat) (p : Polynomial) (priv : List Nat)
    (pres : a∈I ∧ m∈I ∧ z∈I) (am : a≠m) (az : a≠z) (input : (1:Nat)∉priv)
    (common : ∀ i∈removeId a (removeId z (removeId m I)), supported (apart priv) (f i))
    (toNew : ∀ x : Assignment, value x (f a)=0 → value x (f m)=0 → value x (f z)=0 →
      ∃ y, off priv x y ∧ value y p=0)
    (toOld : ∀ x : Assignment, value x p=0 → ∃ y, off priv x y ∧
      value y (f a)=0 ∧ value y (f m)=0 ∧ value y (f z)=0) (X : Rat) :
    project I f X ↔ project (removeId z (removeId m I)) (fun i => if i=a then p else f i) X := by
  constructor
  · rintro ⟨x,hx,old⟩
    obtain ⟨y,hy,row⟩ := toNew x (old a pres.1) (old m pres.2.1) (old z pres.2.2)
    refine ⟨y,(hy 1 input).trans hx,?_⟩
    intro i mem; by_cases h : i=a
    · simpa [h] using row
    · simp only [if_neg h]
      have outside := common i (remove_mem.mpr ⟨mem,h⟩)
      exact (agree_off hy _ outside).trans (old i (remove_mem.mp (remove_mem.mp mem).1).1)
  · rintro ⟨x,hx,new⟩
    have present : a∈removeId z (removeId m I) := remove_mem.mpr ⟨remove_mem.mpr ⟨pres.1,am⟩,az⟩
    obtain ⟨y,hy,first,middle,last⟩ := toOld x (by simpa using new a present)
    refine ⟨y,(hy 1 input).trans hx,?_⟩
    intro i mem
    by_cases h : i=a
    · simpa [h] using first
    by_cases hm : i=m
    · simpa [hm] using middle
    by_cases hz : i=z
    · simpa [hz] using last
    have newmem := remove_mem.mpr ⟨remove_mem.mpr ⟨mem,hm⟩,hz⟩
    have outside := common i (remove_mem.mpr ⟨newmem,h⟩)
    exact (agree_off hy _ outside).trans (by simpa [h] using new i newmem)

theorem identity_numbering (p : Polynomial) : renumber id p=p := by
  induction p with
  | nil => rfl
  | cons h r ih =>
    cases h; simp [renumber,List.map_id_fun] at ih ⊢

theorem parent_project (I : List Nat) (f : Family) (n : Nat) (hn : 1≤n)
    (supp : ∀ r∈I, supported (fun i => decide (1≤i ∧ i≤n)) (f r)) (a : Rat) :
    project I f a ↔ RowsProject n (table I f) a := by
  have bound : ∀ i : Nat, decide (1≤i ∧ i≤n)=true → 1≤id i ∧ id i≤n ∧ id (id i)=i := by
    intro i hi; obtain ⟨lo,h⟩ := of_decide_eq_true hi; exact ⟨lo,h,rfl⟩
  simpa only [identity_numbering] using (compact_project I f _ id id n hn rfl rfl bound supp a)

end ProjectionDescent
