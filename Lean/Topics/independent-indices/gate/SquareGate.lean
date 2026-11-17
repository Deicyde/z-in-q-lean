import InputRestriction

namespace IndependentIndices.SquareGate
open InputRestriction

def shift (t : Rat) := 2*t+1
def value (t : Rat) := 119*(shift t)^2-91
def label (t : Rat) := 2401+(value t)^2

private theorem squarefree119 : Squarefree 119 := by
  intro d h
  have small : d < 11 := by
    have h1 := Nat.le_of_dvd (by decide : 0 < 119) h
    by_cases hd : d < 11
    · exact hd
    · have h2 := Nat.pow_le_pow_left (show 11 ≤ d by omega) 2
      omega
  have finite : ∀ i : Fin 11, i.val^2 ∣ 119 → i.val = 1 := by decide
  exact finite ⟨d,small⟩ h

private theorem one119 (z : Rat) : IsInteger (119*z^2) → IsInteger z := by
  simpa [input, Rat.zero_add] using (reflects_integrality 0 119 squarefree119 z).mp

/-- Odd integral root labels force integral input, including the prime two. -/
theorem integer_of_odd_label (t : Rat) (b : Int) (odd : b % 2 = 1)
    (eq : label t = (b:Rat)) : IsInteger t := by
  have iy : IsInteger ((value t)^2) := by
    refine ⟨b-2401, ?_⟩
    unfold label at eq
    rw [Rat.intCast_sub]; change _=(b:Rat)-2401
    grobner
  obtain ⟨y,hy⟩ := (integer_square_iff _).mp iy
  have bval : b = 2401 + y^2 := by
    apply Rat.intCast_inj.mp
    rw [Rat.intCast_add,Rat.intCast_pow,←hy,←eq]
    rfl
  have is : IsInteger (119*(shift t)^2) := by
    refine ⟨y+91,?_⟩
    unfold value at hy
    rw [Rat.intCast_add]; change _=(y:Rat)+91
    grobner
  obtain ⟨s,hs⟩ := one119 _ is
  have yval : y = 119*s^2-91 := by
    apply Rat.intCast_inj.mp
    rw [Rat.intCast_sub,Rat.intCast_mul,Rat.intCast_pow,←hs,←hy]
    rfl
  have so : s % 2 = 1 := by
    by_cases hc : s % 2 = 1
    · exact hc
    · exfalso
      obtain ⟨k,hk⟩ : ∃ k : Int, s=2*k := ⟨s/2,by omega⟩
      obtain ⟨j,hj⟩ : ∃ j : Int, y=2*j+1 := by
        refine ⟨238*k^2-46,?_⟩
        rw [yval,hk]; grobner
      obtain ⟨j',hj'⟩ : ∃ j' : Int, b=2*j' := by
        refine ⟨1201+2*j^2+2*j,?_⟩
        rw [bval,hj]; grobner
      omega
  refine ⟨s/2,?_⟩
  have hs' : s = 2*(s/2)+1 := by omega
  have rh := congrArg (fun k : Int => (k:Rat)) hs'
  simp only [Rat.intCast_add,Rat.intCast_mul] at rh
  unfold shift at hs
  change (s:Rat) = 2*((s/2 : Int):Rat)+1 at rh
  grobner

theorem odd_label_of_integer (t : Int) :
    ∃ b : Int, b%2=1 ∧ label (t:Rat)=(b:Rat) := by
  let s := 2*t+1
  let y := 119*s^2-91
  refine ⟨2401+y^2,?_,?_⟩
  · have e : y=2*(238*t^2+238*t+14) := by dsimp [y,s]; grobner
    have p : 2401+y^2=2*(1200+2*(238*t^2+238*t+14)^2)+1 := by rw [e]; grobner
    omega
  · dsimp [label,value,shift,y,s]
    simp only [Rat.intCast_add,Rat.intCast_sub,Rat.intCast_mul,Rat.intCast_pow]
    rfl

theorem iff_odd_label (t : Rat) :
    (∃ b : Int, b%2=1 ∧ label t=(b:Rat)) ↔ IsInteger t := by
  constructor
  · rintro ⟨b,odd,eq⟩; exact integer_of_odd_label _ b odd eq
  · rintro ⟨z,rfl⟩; exact odd_label_of_integer z

#print axioms integer_of_odd_label
#print axioms odd_label_of_integer
#print axioms iff_odd_label
end IndependentIndices.SquareGate
