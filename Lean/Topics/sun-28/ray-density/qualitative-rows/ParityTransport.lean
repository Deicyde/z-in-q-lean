import Mathlib.Order.Setoid.Basic

namespace Sun28.QualitativeRows

/-- A walk in a signed graph, carrying the parity of the number of changes. -/
inductive Walk {V : Type*} (edge : V → V → Bool → Prop) : V → V → Bool → Prop where
  | nil (v : V) : Walk edge v v false
  | step {u v w : V} {s t : Bool} :
      Walk edge u v s → edge v w t → Walk edge u w (s ^^ t)

namespace Walk
variable {V : Type*} {edge : V → V → Bool → Prop}

theorem join {u v w : V} {a b : Bool} (first : Walk edge u v a) (second : Walk edge v w b) :
    Walk edge u w (a ^^ b) := by
  induction second with
  | nil => simpa using first
  | step path next ih => simpa only [Bool.xor_assoc] using Walk.step ih next

theorem rev {u v : V} {a : Bool} (path : Walk edge u v a)
    (symm : ∀ {u v b}, edge u v b → edge v u b) : Walk edge v u a := by
  induction path with
  | nil => exact Walk.nil _
  | @step v w s t path next ih =>
    have head : Walk edge w v t := by simpa using Walk.step (Walk.nil w) (symm next)
    simpa only [Bool.xor_comm t s] using head.join ih

end Walk

/-- The two choices at each vertex satisfy all binary constraints precisely
when every closed walk has even parity. Isolated vertices are allowed. -/
theorem balanced_iff {V : Type*} (edge : V → V → Bool → Prop)
    (symm : ∀ {u v b}, edge u v b → edge v u b) :
    (∃ f : V → Bool, ∀ {u v b}, edge u v b → (f u ^^ f v) = b) ↔
    ∀ v, ¬Walk edge v v true := by
  classical
  constructor
  · rintro ⟨f, color⟩
    have sum {u v : V} {d : Bool} (p : Walk edge u v d) : (f u ^^ f v) = d := by
      induction p with
      | nil => simp
      | @step v w a b path next ih =>
        have edge' := color next
        rw [← ih, ← edge']
        cases f u <;> cases f v <;> cases f w <;> decide
    intro v odd
    have impossible := sum odd
    simp at impossible
  · intro no
    let conn : Setoid V :=
      { r := fun u v => ∃ b, Walk edge u v b
        iseqv := ⟨fun u => ⟨_, Walk.nil u⟩, fun ⟨b,h⟩ => ⟨b,h.rev symm⟩,
          fun ⟨_,a⟩ ⟨_,b⟩ => ⟨_,a.join b⟩⟩ }
    let root (u : V) : V := (@Quotient.mk V conn u).out
    have root_path (u : V) : ∃ b, Walk edge (root u) u b :=
      @Quotient.exact V conn _ _ (Quotient.out_eq (@Quotient.mk V conn u))
    choose f path using root_path
    refine ⟨f, ?_⟩
    intro u v b next
    have eq : @Quotient.mk V conn u = @Quotient.mk V conn v :=
      @Quotient.sound V conn u v ⟨b, by simpa using Walk.step (Walk.nil u) next⟩
    have same : root v = root u := congrArg Quotient.out eq.symm
    have reverse := (path v).rev symm
    rw [same] at reverse
    have closed := (Walk.step (path u) next).join reverse
    have even : ((f u ^^ b) ^^ f v) ≠ true := fun h => no (root u) (h ▸ closed)
    cases a : f u <;> cases c : f v <;> cases b <;> simp_all

end Sun28.QualitativeRows

#print axioms Sun28.QualitativeRows.Walk.join
#print axioms Sun28.QualitativeRows.Walk.rev
#print axioms Sun28.QualitativeRows.balanced_iff
