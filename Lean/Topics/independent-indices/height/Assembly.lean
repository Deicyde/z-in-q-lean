import ContactRadicals
import HeightClosure
import LucasDescent
import SquareGate

namespace IndependentIndices.Assembly

def labelSize (ns : Labels) : Nat :=
  max ns.n₁.natAbs (max ns.n₂.natAbs (max ns.n₃.natAbs ns.n₄.natAbs))

def multiplicativeHeight (x : Rat) : Nat := max x.num.natAbs x.den

def rootConstant : Nat :=
  2 * HeightClosure.constant [2,3,5,7,11,13,17,29,37,41,2399]

def anchorModulus : Nat := 2 * 3^1474

def observedMaximum {ns : Labels} {B : Rat} (f g h : Frame ns B) : Nat :=
  largest (radical f.primes) (radical g.primes) (radical h.primes)

/-- The canonical reduced denominator is already included in the multiplicative height. -/
theorem numerator_magnitude (x : Rat) (n : Int) (l : Nat)
    (hn : n.natAbs ≤ l) (hl : 1 ≤ l) :
    (((n : Rat)-x).num).natAbs ≤ 2*l*multiplicativeHeight x := by
  rw [reduced_num]
  have hx : x.num.natAbs ≤ multiplicativeHeight x := Nat.le_max_left ..
  have hd : x.den ≤ multiplicativeHeight x := Nat.le_max_right ..
  have one := Nat.mul_le_mul_right (multiplicativeHeight x) hl
  rw [Nat.one_mul] at one
  calc
    _ ≤ (n*(x.den:Int)).natAbs+x.num.natAbs := Int.natAbs_sub_le ..
    _ = n.natAbs*x.den+x.num.natAbs := by rw [Int.natAbs_mul,Int.natAbs_natCast]
    _ ≤ l*multiplicativeHeight x+l*multiplicativeHeight x :=
      Nat.add_le_add (Nat.mul_le_mul hn hd) (Nat.le_trans hx one)
    _ = _ := by grobner

/-- The signs of all three Lucas labels are arbitrary. -/
theorem lucas_magnitude (a t z : Int) (l : Nat) (hl : 4 ≤ l)
    (ha : a.natAbs ≤ l) (ht : t.natAbs ≤ l) (hz : z.natAbs ≤ l) :
    (lucas a t z).natAbs ≤ 5*l^4 := by
  have hshift : (a-2).natAbs ≤ l+2 :=
    Nat.le_trans (Int.natAbs_sub_le ..) (Nat.add_le_add_right ha 2)
  have h₁ : (t*t).natAbs ≤ l*l := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul ht ht
  have h₂ : (a*(a-2)*t*z).natAbs ≤ l*(l+2)*l*l := by
    simp only [Int.natAbs_mul]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha hshift) ht) hz
  have h₃ : ((a-2)*(a-2)*z*z).natAbs ≤ (l+2)*(l+2)*l*l := by
    simp only [Int.natAbs_mul]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hshift hshift) hz) hz
  have triangle (x y w : Int) :
      (x-y+w-1).natAbs ≤ x.natAbs+y.natAbs+w.natAbs+1 := by
    have hxy := Int.natAbs_sub_le x y
    have hxyw := Int.natAbs_add_le (x-y) w
    have hlast := Int.natAbs_sub_le (x-y+w) 1
    rw [Int.natAbs_one] at hlast
    omega
  calc
    _ ≤ (t*t).natAbs+(a*(a-2)*t*z).natAbs+((a-2)*(a-2)*z*z).natAbs+1 :=
      triangle ..
    _ ≤ l*l+l*(l+2)*l*l+(l+2)*(l+2)*l*l+1 :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃) 1
    _ ≤ 5*l^4 := by
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hl
      subst l
      have eqn : 5*(4+k)^4 =
          (4+k)*(4+k)+(4+k)*(4+k+2)*(4+k)*(4+k)
          +(4+k+2)*(4+k+2)*(4+k)*(4+k)+1
          +(3*k^4+42*k^3+211*k^2+440*k+303) := by grobner
      rw [eqn]
      exact Nat.le_add_right ..

/-- Signed Lucas growth gives the exponential integer separation used by the numerator step. -/
theorem exponential_size {a t z : Int} (ha : 7 ≤ a.natAbs) (hz : z ≠ 0)
    (hf : lucas a t z=0) : 2^(a.natAbs-4) ≤ t.natAbs := by
  have sol : LucasDescent.LabelSol a t z := by
    unfold lucas at hf
    unfold LucasDescent.LabelSol
    grobner
  obtain ⟨lo,hi⟩ := LucasDescent.signed_growth ha hz sol
  have intBound := Int.lt_of_lt_of_le lo hi
  have bound : (3:Nat)^(a.natAbs-3) < t.natAbs := Int.ofNat_lt.mp intBound
  exact Nat.le_trans (Nat.pow_le_pow_left (by decide : 2≤3) _)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide : 0<3) (by omega)) (Nat.le_of_lt bound))

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 8192 in
/-- The input is integral once the three residue frames, the two height bounds,
    the odd label and the nonvanishing and anchor hypotheses have been supplied. -/
theorem integral_of_frames (x : Rat) (ns : Labels) (f g h : Frame ns (SquareGate.label x))
    (odd : ns.n₁ % 2 = 1) (last_nonzero : ns.n₄ ≠ 0)
    (anchor_nonzero : ns.n₂-1 ≠ 0) (anchor : (anchorModulus:Int) ∣ ns.n₂-1)
    (root_height : (labelSize ns)^2 < rootConstant*(observedMaximum f g h)^17)
    (scalar_height : (multiplicativeHeight (SquareGate.label x))^17 ≤ 2^(ns.n₂.natAbs-4)) :
    lucas ns.n₂ ns.n₃ ns.n₄=0 ∧ SquareGate.label x=(ns.n₁ : Rat) ∧ InputRestriction.IsInteger x := by
  have sizes : ns.n₁.natAbs ≤ labelSize ns ∧ ns.n₂.natAbs ≤ labelSize ns ∧
      ns.n₃.natAbs ≤ labelSize ns ∧ ns.n₄.natAbs ≤ labelSize ns := by
    unfold labelSize
    omega
  obtain ⟨h₁,h₂,h₃,h₄⟩ := sizes
  have aLower : anchorModulus ≤ (ns.n₂-1).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr anchor_nonzero) (Int.ofNat_dvd_left.mp anchor)
  have shift := Int.natAbs_sub_le ns.n₂ 1
  rw [Int.natAbs_one] at shift
  have large : anchorModulus-1 ≤ ns.n₂.natAbs := by omega
  have bounds : 5^17*rootConstant^40 < (anchorModulus-1)^12 ∧
      80*HeightClosure.constant [2,3,5,7,17]*19^17 < anchorModulus ∧
      10000 < anchorModulus-1 ∧ 2^17*rootConstant^10 < (2^4000)^2 :=
    HeightClosure.numerical_bounds
  have largeLabel : 10000 < ns.n₂.natAbs := Nat.lt_of_lt_of_le bounds.2.2.1 large
  have rootAnchor := Nat.lt_of_lt_of_le bounds.1 (Nat.pow_le_pow_left (Nat.le_trans large h₂) 12)
  have divs := (three_frames f g h).2
  have endgame := HeightClosure.two_defects root_height rootAnchor
    (lucas_magnitude _ _ _ _ (by omega) h₂ h₃ h₄) divs.1 divs.2
    (numerator_magnitude _ _ _ h₁ (by omega)) (by
      intro zero
      have huge := Nat.le_trans (exponential_size (by omega) last_nonzero zero) h₃
      have hbase : 2^4000 ≤ labelSize ns :=
        Nat.le_trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega)) huge
      exact ⟨Nat.lt_of_lt_of_le bounds.2.2.2 (Nat.pow_le_pow_left hbase 2),
        Nat.le_trans scalar_height huge⟩)
  have zero := Rat.num_eq_zero.mp endgame.2
  have equal : SquareGate.label x=(ns.n₁ : Rat) := by grobner
  exact ⟨endgame.1,equal,SquareGate.integer_of_odd_label x _ odd equal⟩

#print axioms numerator_magnitude
#print axioms lucas_magnitude
#print axioms exponential_size
#print axioms integral_of_frames

end IndependentIndices.Assembly
