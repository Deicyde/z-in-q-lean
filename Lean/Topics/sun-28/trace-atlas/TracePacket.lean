import TraceArguments

namespace Sun28.TraceAtlas
open ZInQ GroupCharts Forward Ordinary ScalarHeight WitnessIndices
noncomputable section
variable {R : Type*} [CommRing R]

def frac (x : Quad R) : R × R := (x.re,x.den)
def val (φ : R →+* ℚ) (f : R × R) : ℚ := φ f.1 / φ f.2
def Guards (φ : R →+* ℚ) (l : List R) : Prop := ∀ g ∈ l, φ g≠0

private theorem guards_nil (φ : R →+* ℚ) : Guards φ [] := by simp [Guards]
private theorem guards_cons (φ : R →+* ℚ) (a : R) (l : List R) :
    Guards φ (a::l) ↔ φ a≠0 ∧ Guards φ l := List.forall_mem_cons
private theorem guards_append (φ : R →+* ℚ) (a b : List R) :
    Guards φ (a++b) ↔ Guards φ a ∧ Guards φ b := List.forall_mem_append

private theorem guard_ne {φ : R →+* ℚ} {a : E R} {x : ℚ} (h : RatValue φ a x) :
    φ (Program.eval φ a).re≠0 ↔ x≠0 := by
  obtain ⟨d,v⟩ := fraction_value φ h
  rw [←v]
  simp [d]

private theorem mark_ne (t : ℚ) : fiveProduct t≠0 ↔ t∉marks := by
  unfold fiveProduct
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h mem
    exact h t mem (sub_self t)
  · intro h a mem e
    exact h ((sub_eq_zero.mp e) ▸ mem)

structure OrdOutput (R : Type*) where
  guards : List R
  b : R × R

/-- One scale. Each branching rational expression is selected once and its output reused. -/
def ordOutput (p : Codes R) (M : ℕ) (c : ℤ) (b η : E R) (j : Fin 3) : Program R (OrdOutput R) :=
  Program.bind (fun a =>
    let s : E R := .pure a
    let A := power s 2
    Program.bind (fun t =>
      let T : E R := .pure t
      Program.bind (fun marks =>
        Program.bind (fun tr =>
          Program.bind (fun v => .pure ⟨[a.re,t.re-3*t.den,marks.re,tr.re],frac v⟩)
            (div (detection A T) (power (.pure tr) 2)))
          (trace p M c b A T))
        (markProd T))
      (mul A η)) (scales p M j)

def side (s η : ℚ) : Prop := s^2*η∉marks ∧ s^2*η≠3 ∧ s≠0

attribute [local irreducible] trace detection scales markProd power mul div in
theorem ordOutput_spec {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
    (M : ℕ) (c : ℤ) {b η : E R} {β h : ℚ} (hb : RatValue φ b β) (hη : RatValue φ η h) (j : Fin 3) :
    let u := Program.eval φ (ordOutput p M c b η j)
    let s := pointScale w M j
    let A := s^2
    let t := A*h
    let H := ordinaryTraceAt w M c β A t
    (Guards φ u.guards ↔ side s h ∧ H≠0) ∧ φ u.b.2≠0 ∧ val φ u.b=detector A t/H^2 := by
  let sc := Program.eval φ (scales p M j)
  let s := pointScale w M j
  have sv : RatValue φ (.pure sc) s := scales_correct hp M j
  let A := power (.pure sc) 2
  have av : RatValue φ A (s^2) := RatValue.power sv 2
  let tc := Program.eval φ (mul A η)
  let t := s^2*h
  have tv : RatValue φ (.pure tc) t := RatValue.mul av hη
  let T : E R := .pure tc
  let tr := Program.eval φ (trace p M c b A T)
  let v := ordinaryTraceAt w M c β (s^2) t
  have hv : RatValue φ (.pure tr) v := trace_correct hp M c hb av tv
  have mk : φ (Program.eval φ (markProd T)).re≠0 ↔ fiveProduct t≠0 := guard_ne (marks_correct tv)
  have sg : φ sc.re≠0 ↔ s≠0 := guard_ne sv
  have tg : φ tr.re≠0 ↔ v≠0 := guard_ne hv
  have tt : φ (tc.re-3*tc.den)≠0 ↔ t≠3 := by
    obtain ⟨hd,he⟩ := fraction_value φ tv
    change φ tc.den≠0 at hd
    change φ tc.re / φ tc.den=t at he
    rw [map_sub,map_mul,map_ofNat,←he,ne_eq,sub_eq_zero,ne_eq,div_eq_iff hd]
  have bs := RatValue.div (detector_correct av tv) (RatValue.power hv 2)
  have checks := fraction_value φ bs
  dsimp only
  simp only [ordOutput,Program.eval_bind,Program.eval]
  refine ⟨?_,checks.1,checks.2⟩
  change Guards φ [sc.re,tc.re-3*tc.den,(Program.eval φ (markProd T)).re,tr.re] ↔ _
  simp only [guards_cons,guards_nil,and_true]
  rw [sg,tt,mk,mark_ne,tg]
  change (s≠0 ∧ t≠3 ∧ t∉marks ∧ v≠0) ↔ ((t∉marks ∧ t≠3 ∧ s≠0) ∧ v≠0)
  tauto

structure ScalarOutput (R : Type*) where
  guard : R
  b : R × R

def scalarOutput (p : Codes R) (M : ℕ) (r Γ : E R) (D : ℕ) (pos : Bool) : Program R (ScalarOutput R) :=
  Program.bind (fun g => Program.bind (fun B => .pure ⟨g.re,frac B⟩)
    (scalarB r Γ (.pure g) D pos)) (tree p M r)

attribute [local irreducible] tree scalarB in
theorem scalarOutput_spec {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
    (M : ℕ) {r Γ : E R} {v γ : ℚ} (hr : RatValue φ r v) (hΓ : RatValue φ Γ γ) (D : ℕ) (pos : Bool) :
    let u := Program.eval φ (scalarOutput p M r Γ D pos)
    let t := scalarTree v (scalarEntries w M)
    (φ u.guard≠0 ↔ t≠0) ∧ φ u.b.2≠0 ∧ val φ u.b=signedValue v (sign pos) γ D t := by
  have tv := tree_correct hp M hr
  have sel : RatValue φ (.pure (Program.eval φ (tree p M r))) _ := tv
  have value := fraction_value φ (scalarB_correct hr hΓ sel D pos)
  simp only [scalarOutput,Program.eval_bind,Program.eval]
  exact ⟨guard_ne tv,value⟩

structure Packet (R : Type*) where
  guards : List R
  ordinary : Fin 3 → R × R
  scalar : R × R

def assemble (a b d : OrdOutput R) (s : ScalarOutput R) : Packet R :=
  ⟨a.guards++b.guards++d.guards++[s.guard],![a.b,b.b,d.b],s.b⟩

def packet (p : Codes R) (M : ℕ) (c : ℤ) (x η Γ : E R) (D : ℕ) (pos : Bool) : Program R (Packet R) :=
  let b := βcode x
  let o := ordOutput p M c b η
  Program.bind (fun a => Program.bind (fun b₁ => Program.bind (fun d =>
    Program.bind (fun s => .pure (assemble a b₁ d s)) (scalarOutput p M (rad b) Γ D pos)) (o 2)) (o 1)) (o 0)

private theorem guards_assemble (φ : R →+* ℚ) (o : Fin 3 → OrdOutput R) (s : ScalarOutput R) :
    Guards φ (assemble (o 0) (o 1) (o 2) s).guards ↔ (∀ j, Guards φ (o j).guards) ∧ φ s.guard≠0 := by
  simp only [assemble,guards_append,guards_cons,guards_nil,and_true]
  constructor
  · rintro ⟨⟨⟨a,b⟩,c⟩,d⟩
    exact ⟨fun j => by fin_cases j <;> first | exact a | exact b | exact c,d⟩
  · rintro ⟨o,d⟩
    exact ⟨⟨⟨o 0,o 1⟩,o 2⟩,d⟩

structure PacketSpec (φ : R →+* ℚ) (a : Packet R) (w : NinePoints) (M : ℕ) (c : ℤ)
    (x η Γ : ℚ) (D : ℕ) (pos : Bool) : Prop where
  guards : Guards φ a.guards ↔
    (∀ j, let s:=pointScale w M j; side s η ∧ ordinaryTraceAt w M c (beta x) (s^2) (s^2*η)≠0) ∧
      scalarTree (scalarRadicand (beta x)) (scalarEntries w M)≠0
  ordinary : ∀ j, let s:=pointScale w M j; let t:=s^2*η
    φ (a.ordinary j).2≠0 ∧ val φ (a.ordinary j)=detector (s^2) t/(ordinaryTraceAt w M c (beta x) (s^2) t)^2
  scalar : φ a.scalar.2≠0 ∧ val φ a.scalar = signedValue (scalarRadicand (beta x)) (sign pos) Γ D
    (scalarTree (scalarRadicand (beta x)) (scalarEntries w M))

attribute [local irreducible] ordOutput scalarOutput βcode rad pointScale ordinaryTraceAt scalarTree in
theorem packet_spec {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
    (M : ℕ) (c : ℤ) {x η Γ : E R} {a h γ : ℚ} (hx : RatValue φ x a)
    (hη : RatValue φ η h) (hΓ : RatValue φ Γ γ) (D : ℕ) (pos : Bool) :
    PacketSpec φ (Program.eval φ (packet p M c x η Γ D pos)) w M c a h γ D pos := by
  let o := fun j => Program.eval φ (ordOutput p M c (βcode x) η j)
  let s := Program.eval φ (scalarOutput p M (rad (βcode x)) Γ D pos)
  have bo := beta_correct hx
  have oh := fun i => ordOutput_spec hp M c bo hη i
  have sh := scalarOutput_spec hp M (rad_correct bo) hΓ D pos
  simp only [packet,Program.eval_bind,Program.eval]
  change PacketSpec φ (assemble (o 0) (o 1) (o 2) s) _ _ _ _ _ _ _ _
  constructor
  · rw [guards_assemble]
    exact and_congr (forall_congr' fun i => (oh i).1) sh.1
  · intro j
    fin_cases j <;> first | exact (oh 0).2 | exact (oh 1).2 | exact (oh 2).2
  · exact sh.2

end
#print axioms ordOutput_spec
#print axioms scalarOutput_spec
#print axioms packet_spec
end Sun28.TraceAtlas
