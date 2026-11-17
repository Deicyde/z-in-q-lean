import Std

namespace InputRestriction

/-- The image of the usual embedding of the integers in the rationals. -/
def IsInteger (x : Rat) : Prop := ∃ n : Int, x=(n:Rat)

/-- A natural number is squarefree if its only square divisor is `1`. -/
def Squarefree (m : Nat) : Prop := ∀ d : Nat, d^2 ∣ m → d=1

def input (r m : Int) (x : Rat) : Rat := (r:Rat)+(m:Rat)*x^2

theorem integer_iff_den_one (x : Rat) : IsInteger x ↔ x.den=1 := by
  constructor
  · rintro ⟨n,rfl⟩; rfl
  · intro d; exact ⟨x.num,Rat.ext rfl d⟩

private theorem cross (m n : Int) (x : Rat) :
    (m:Rat)*x=(n:Rat) ↔ m*x.num=n*(x.den:Int) := by
  have rep : mkRat n 1=(n:Rat) := by simpa only [Rat.num_intCast,Rat.den_intCast] using Rat.mkRat_self (n:Rat)
  rw [Rat.mul_def',Rat.num_intCast,Rat.den_intCast,Nat.one_mul,←rep,Rat.mkRat_eq_iff x.den_nz Nat.one_ne_zero]
  simp

/-- Exact denominator test, with no hypothesis on the sign or the vanishing of `m`. -/
theorem integer_mul_iff (m : Int) (x : Rat) : IsInteger ((m:Rat)*x) ↔ x.den ∣ m.natAbs := by
  constructor
  · rintro ⟨n,eq⟩
    have absEq := congrArg Int.natAbs ((cross m n x).mp eq)
    have d : m.natAbs*x.num.natAbs=n.natAbs*x.den := by simpa only [Int.natAbs_mul,Int.natAbs_natCast] using absEq
    apply x.reduced.symm.dvd_of_dvd_mul_right
    exact ⟨n.natAbs,d.trans (Nat.mul_comm _ _)⟩
  · intro h
    obtain ⟨c,hc⟩ := Int.ofNat_dvd_left.mpr h
    exact ⟨c*x.num,(cross m _ x).mpr (by rw [hc];grobner)⟩

private theorem integer_translate (r : Int) (y : Rat) : IsInteger ((r:Rat)+y) ↔ IsInteger y := by
  constructor
  · rintro ⟨n,eq⟩;exact ⟨n-r,by rw [Rat.intCast_sub];grobner⟩
  · rintro ⟨n,rfl⟩;exact ⟨r+n,(Rat.intCast_add ..).symm⟩

/-- In lowest terms `x=a/d`, the shifted quadratic is integral exactly when `d² ∣ |m|`. -/
theorem denominator_criterion (r m : Int) (x : Rat) : IsInteger (input r m x) ↔ x.den^2 ∣ m.natAbs := by
  unfold input
  rw [integer_translate,integer_mul_iff,Rat.den_pow]

theorem reflects_integrality (r m : Int) (sf : Squarefree m.natAbs) (x : Rat) :
    IsInteger (input r m x) ↔ IsInteger x := by
  constructor
  · intro h;exact (integer_iff_den_one x).mpr (sf _ ((denominator_criterion r m x).mp h))
  · rintro ⟨n,rfl⟩;exact ⟨r+m*n^2,by simp [input,Rat.intCast_add,Rat.intCast_mul,Rat.intCast_pow]⟩

/-- Squarefreeness is necessary as well when the target is the whole image of the integers. -/
theorem reflection_iff_squarefree (r m : Int) :
    (∀ x : Rat, IsInteger (input r m x) → IsInteger x) ↔ Squarefree m.natAbs := by
  constructor
  · intro reflect
    have positive (d : Nat) (nz : d≠0) (divides : d^2 ∣ m.natAbs) : d=1 := by
      let x := mkRat 1 d
      have den : x.den=d := by simp [x,Rat.den_mkRat,nz]
      have inside := reflect x ((denominator_criterion r m x).mpr (den ▸ divides))
      exact den ▸ (integer_iff_den_one x).mp inside
    intro d dvd
    by_cases zero : d=0
    · have killed : m.natAbs=0 := by simpa [zero] using dvd
      have bad := positive 2 (by decide) (by rw [killed];exact Nat.dvd_zero _)
      omega
    · exact positive d zero dvd
  · intro sf x;exact (reflects_integrality r m sf x).mp

/-- Soundness of `A` and coverage of the integer values in the indicated progression suffice. -/
theorem preimage (A : Rat→Prop) (r m : Int) (sf : Squarefree m.natAbs)
    (sound : ∀ y, A y → IsInteger y) (cover : ∀ n : Int, A (input r m (n:Rat))) (x : Rat) :
    A (input r m x) ↔ IsInteger x := by
  constructor
  · exact fun h => (reflects_integrality r m sf x).mp (sound _ h)
  · rintro ⟨n,rfl⟩;exact cover n

private theorem one_squarefree : Squarefree 1 := by
  intro d hd
  have divides : d ∣ d^2 := by simpa [Nat.pow_succ] using Nat.dvd_mul_right d d
  exact Nat.eq_one_of_dvd_one (Nat.dvd_trans divides hd)

theorem integer_square_iff (x : Rat) : IsInteger (x^2) ↔ IsInteger x := by
  simpa [input,Rat.one_mul,Rat.zero_add] using reflects_integrality 0 1 one_squarefree x

/-- A marked predicate already supplies the zero member of the square progression. -/
theorem marked_squares (A : Rat→Prop) (sound : ∀ y, A y → IsInteger y) (marked : A 0)
    (nonzero : ∀ n : Int, n≠0 → A ((n:Rat)^2)) (x : Rat) : A (x^2) ↔ IsInteger x := by
  constructor
  · exact fun h => (integer_square_iff x).mp (sound _ h)
  · rintro ⟨n,rfl⟩
    by_cases hn : n=0
    · subst n; simpa only [show (0:Int).cast (R:=Rat)=0 by rfl,show (0:Rat)^2=0 by grobner] using marked
    · exact nonzero n hn

/-- For a sound marked predicate, covering the nonzero integer squares is also necessary. -/
theorem marked_criterion (A : Rat→Prop) (sound : ∀ y, A y → IsInteger y) (marked : A 0) :
    (∀ x : Rat, A (x^2) ↔ IsInteger x) ↔ ∀ n : Int, n≠0 → A ((n:Rat)^2) := by
  constructor
  · intro all n _; exact (all (n:Rat)).mpr ⟨n,rfl⟩
  · exact marked_squares A sound marked

#print axioms denominator_criterion
#print axioms reflection_iff_squarefree
#print axioms reflects_integrality
#print axioms preimage
#print axioms integer_square_iff
#print axioms marked_squares
#print axioms marked_criterion

end InputRestriction
