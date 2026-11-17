import TracePacket

namespace Sun28.TraceAtlas
open ZInQ GroupCharts Forward Ordinary ScalarHeight WitnessIndices
noncomputable section
variable {R : Type*} [CommRing R]

/-- The two continuous parameters for each of the four rational pole tests stay fixed. -/
def Accepts (φ : R →+* ℚ) (a : Packet R) (Uo Us : Finset ℚ)
    (e z : Fin 3 → ℚ) (eS zS : ℚ) : Prop :=
  Guards φ a.guards ∧ (∀ j, poleAt Uo (val φ (a.ordinary j)) (e j) (z j)) ∧
    poleAt Us (val φ a.scalar) eS zS

theorem packet_at {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
    (M : ℕ) (c : ℤ) {x η Γ : E R} {a h γ : ℚ} (hx : RatValue φ x a)
    (hη : RatValue φ η h) (hΓ : RatValue φ Γ γ) (D : ℕ) (Uo Us : Finset ℚ)
    (e z : Fin 3 → ℚ) (eS zS : ℚ) :
    (∃ pos : Bool, Accepts φ (Program.eval φ (packet p M c x η Γ D pos)) Uo Us e z eS zS) ↔
      (∀ j, side (pointScale w M j) h) ∧
      (∀ j, let s := pointScale w M j; ordinaryAtPair w M c (beta a) (s^2) (s^2*h) Uo (e j) (z j)) ∧
      scalarAtPair w M (scalarRadicand (beta a)) γ D Us eS zS := by
  have spec := fun pos => packet_spec hp M c hx hη hΓ D pos
  constructor
  · rintro ⟨pos,guards,o,s⟩
    obtain ⟨all,sg⟩ := (spec pos).guards.1 guards
    refine ⟨fun j => (all j).1,?_,?_⟩
    · intro j
      exact ⟨(all j).2,((spec pos).ordinary j).2 ▸ o j⟩
    ·
      refine ⟨sign pos,?_,sg,(spec pos).scalar.2 ▸ s⟩
      cases pos <;> simp [sign]
  · rintro ⟨guard,ord,δ,eq,sg,sc⟩
    obtain ⟨pos,ep⟩ : ∃ pos : Bool, sign pos=δ := by
      rcases eq with rfl|rfl
      · exact ⟨true,rfl⟩
      · exact ⟨false,rfl⟩
    refine ⟨pos,(spec pos).guards.2 ⟨fun j => ⟨guard j,(ord j).1⟩,sg⟩,?_,?_⟩
    · intro j
      rw [((spec pos).ordinary j).2]
      exact (ord j).2
    · rw [(spec pos).scalar.2,ep]
      exact sc

/-- A free rational slot has denominator one and zero irrational part. -/
def slot (r : R) : E R := .pure (.ofPair r 0)

theorem slot_spec (φ : R →+* ℚ) (r : R) : RatValue φ (slot r) (φ r) := by
  refine ⟨Quad.good_pair φ r 0,?_⟩
  change Quad.eval φ (Quad.ofPair r 0)=_
  rw [Quad.eval_pair,map_zero]
  rfl

end
#print axioms packet_at
#print axioms slot_spec
end Sun28.TraceAtlas
