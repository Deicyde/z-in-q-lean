module

public import Std

@[expose] public section

namespace CentralSpecialization

open Lean.Grind

private theorem sub_chain {A} [IntModule A] (a b c : A) :
    (a-b)+(b-c) = a-c := by
  simp only [AddCommGroup.sub_eq_add_neg]
  rw [AddCommMonoid.add_assoc, ← AddCommMonoid.add_assoc (-b) b (-c),
    AddCommGroup.neg_add_cancel, AddCommMonoid.zero_add]

private theorem sum_differences {A} [IntModule A] (a b c d : A) :
    (a-b)+(c-d) = (a+c)-(b+d) := by
  simp only [AddCommGroup.sub_eq_add_neg, AddCommGroup.neg_add]
  rw [AddCommMonoid.add_assoc a (-b) (c + -d), AddCommMonoid.add_left_comm (-b) c (-d),
    ← AddCommMonoid.add_assoc]

/-- An additive map between abelian groups, written in Std's integer-module notation. -/
structure AddMap (A : Type u) (B : Type v) [IntModule A] [IntModule B] where
  apply : A → B
  map_zero : apply 0 = 0
  map_add (x y : A) : apply (x + y) = apply x + apply y

private theorem map_nsmul {A B} [IntModule A] [IntModule B] (f : AddMap A B)
    (k : Nat) (x : A) : f.apply (k • x) = k • f.apply x := by
  induction k with
  | zero => simp only [NatModule.zero_nsmul, f.map_zero]
  | succ k ih => rw [NatModule.add_one_nsmul, f.map_add, ih, NatModule.add_one_nsmul]

private theorem map_sub {A B} [IntModule A] [IntModule B] (f : AddMap A B)
    (x y : A) : f.apply (x - y) = f.apply x - f.apply y := by
  apply (AddCommGroup.sub_eq_iff.mpr ?_).symm
  rw [← f.map_add, AddCommGroup.sub_add_cancel]

private theorem nsmul_sub {A} [IntModule A] (k : Nat) (x y : A) :
    k • (x-y) = k • x - k • y := by
  rw [← IntModule.zsmul_natCast_eq_nsmul, IntModule.zsmul_sub,
    IntModule.zsmul_natCast_eq_nsmul, IntModule.zsmul_natCast_eq_nsmul]

/-- Only preservation of sums and the composition law of a left action are used. -/
structure PointAction (G : Type u) (A : Type v) [Mul G] [IntModule A] where
  map : G → AddMap A A
  compose (g h : G) (x : A) : (map (g*h)).apply x = (map g).apply ((map h).apply x)

private theorem point_difference_cocycle {G A} [Mul G] [IntModule A] (act : PointAction G A)
    (P : A) (g h : G) :
    (act.map (g*h)).apply P-P =
      ((act.map g).apply P-P) + (act.map g).apply ((act.map h).apply P-P) := by
  rw [act.compose, map_sub, AddCommMonoid.add_comm ((act.map g).apply P-P)]
  exact (sub_chain _ _ _).symm

/-- Every point killed by a power of two is killed by two. -/
def TwoPrimaryExponentTwo (A : Type u) [IntModule A] : Prop :=
  ∀ (k : Nat) (x : A), (2^k : Nat) • x = 0 → (2 : Nat) • x = 0

/-- A choice of upper-field preimages of (g-1)P at the extra bit of precision. -/
def ExtraBitLift {G A} [Mul G] [IntModule A] (act : PointAction G A)
    (m : Nat) (P : A) (V : G → A) : Prop :=
  ∀ g, (2^(m+1) : Nat) • V g = (act.map g).apply P - P

/-- If two extra-bit preimages have the same multiple, their doubles coincide. -/
theorem doubled_lift_unique {A} [IntModule A] (torsion : TwoPrimaryExponentTwo A)
    (m : Nat) {v w : A} (h : (2^(m+1) : Nat) • v = (2^(m+1) : Nat) • w) :
    (2 : Nat) • v = (2 : Nat) • w := by
  apply AddCommGroup.sub_eq_zero_iff.mp
  rw [← nsmul_sub]
  apply torsion (m+1)
  rw [nsmul_sub, h, AddCommGroup.sub_self]

/-- The double of an upper-bit preimage is the unique *even* point over the target
at the lower precision. Other, non-even preimages are not excluded. -/
theorem unique_even_preimage {A} [IntModule A] (torsion : TwoPrimaryExponentTwo A)
    (m : Nat) (y v : A) (hv : (2^(m+1) : Nat) • v = y) :
    (2^m : Nat) • ((2 : Nat) • v) = y ∧
    ∀ w : A, (∃ u : A, w = (2 : Nat) • u) → (2^m : Nat) • w = y → w = (2 : Nat) • v := by
  constructor
  · rw [← NatModule.mul_nsmul, ← Nat.pow_succ, hv]
  · intro w hw hy
    obtain ⟨u, hu⟩ := hw
    subst w
    apply doubled_lift_unique torsion m
    rw [hv, Nat.pow_succ, NatModule.mul_nsmul]
    exact hy

/-- Doubling an extra-bit lift yields precisely the required multiple at level m. -/
theorem doubled_lift_multiple {G A} [Mul G] [IntModule A] {act : PointAction G A}
    {m : Nat} {P : A} {V : G → A} (hV : ExtraBitLift act m P V) (g : G) :
    (2^m : Nat) • ((2 : Nat) • V g) = (act.map g).apply P - P := by
  rw [← NatModule.mul_nsmul, ← Nat.pow_succ]
  exact hV g

/-- The doubles are an exact (inhomogeneous) 1-cocycle, in the point group itself. -/
theorem doubled_lift_cocycle {G A} [Mul G] [IntModule A] (torsion : TwoPrimaryExponentTwo A)
    {act : PointAction G A} {m : Nat} {P : A} {V : G → A}
    (hV : ExtraBitLift act m P V) (g h : G) :
    (2 : Nat) • V (g*h) = (2 : Nat) • V g + (act.map g).apply ((2 : Nat) • V h) := by
  rw [map_nsmul, ← NatModule.nsmul_add]
  apply doubled_lift_unique torsion m
  rw [hV, NatModule.nsmul_add, ← map_nsmul, hV g, hV h]
  exact point_difference_cocycle act P g h

/-- Arbitrary upper-bit choices for P, Q and P+Q give additive doubles. -/
theorem doubled_lift_additive {G A} [Mul G] [IntModule A] (torsion : TwoPrimaryExponentTwo A)
    {act : PointAction G A} {m : Nat} {P Q : A} {V W Z : G → A}
    (hV : ExtraBitLift act m P V) (hW : ExtraBitLift act m Q W)
    (hZ : ExtraBitLift act m (P+Q) Z) (g : G) :
    (2 : Nat) • Z g = (2 : Nat) • V g + (2 : Nat) • W g := by
  rw [← NatModule.nsmul_add]
  apply doubled_lift_unique torsion m
  rw [hZ, NatModule.nsmul_add, hV, hW, (act.map g).map_add]
  exact (sum_differences _ _ _ _).symm

/-- The canonical doubles commute with any equivariant additive map. -/
theorem doubled_lift_natural {G A B} [Mul G] [IntModule A] [IntModule B]
    (torsion : TwoPrimaryExponentTwo B) (f : AddMap A B)
    {actA : PointAction G A} {actB : PointAction G B}
    (equiv : ∀ g x, f.apply ((actA.map g).apply x) = (actB.map g).apply (f.apply x))
    {m : Nat} {P : A} {V : G → A} {W : G → B}
    (hV : ExtraBitLift actA m P V) (hW : ExtraBitLift actB m (f.apply P) W) (g : G) :
    f.apply ((2 : Nat) • V g) = (2 : Nat) • W g := by
  rw [map_nsmul]
  apply doubled_lift_unique torsion m
  rw [← map_nsmul, hV, hW, map_sub, equiv]

/-- When both extra-bit conditions hold in one fixed diagram, doubling
the (m+1)-level correction gives the m-level correction. -/
theorem doubled_lift_precision {G A} [Mul G] [IntModule A] (torsion : TwoPrimaryExponentTwo A)
    {act : PointAction G A} {m : Nat} {P : A} {V W : G → A}
    (low : ExtraBitLift act m P V) (high : ExtraBitLift act (m+1) P W) (g : G) :
    (2 : Nat) • V g = (2 : Nat) • ((2 : Nat) • W g) := by
  apply doubled_lift_unique torsion m
  rw [low, ← NatModule.mul_nsmul, ← Nat.pow_succ, high]

/-- In the group containing a division point R, correct its coboundary by the
inflated W. The ambient group need not have exponent-two primary torsion. -/
theorem corrected_kummer_cocycle {G A} [Mul G] [IntModule A] (act : PointAction G A)
    (m : Nat) (P R : A) (W : G → A)
    (hR : (2^m : Nat) • R = P)
    (multiple : ∀ g, (2^m : Nat) • W g = (act.map g).apply P - P)
    (cocycle : ∀ g h, W (g*h) = W g + (act.map g).apply (W h)) :
    let b := fun g => ((act.map g).apply R - R) - W g
    (∀ g h, b (g*h) = b g + (act.map g).apply (b h)) ∧
    (∀ g, (2^m : Nat) • b g = 0) := by
  dsimp only
  constructor
  · intro g h
    rw [point_difference_cocycle act R g h, cocycle,
      map_sub (act.map g) ((act.map h).apply R - R) (W h)]
    exact (sum_differences _ _ _ _).symm
  · intro g
    rw [nsmul_sub, nsmul_sub, ← map_nsmul, hR, multiple, AddCommGroup.sub_self]

/-- Entrywise arithmetic for a determinant-one 2-adic matrix, using only the
required congruences of integer representatives. The trace of the square differs from
+2 and −2 by multiples of exactly 2^6 and 2^2, respectively. -/
theorem matrix_square_trace (a b c d : Int)
    (hdet : 64 ∣ a*d-b*c-1) (htrace : 32 ∣ a+d+14) :
    let s := a*a+b*c+c*b+d*d
    s % 128 = 66 ∧ (64 ∣ s-2) ∧ ¬ (128 ∣ s-2) ∧ (4 ∣ s+2) ∧ ¬ (8 ∣ s+2) := by
  dsimp only
  obtain ⟨j, hj⟩ := hdet
  obtain ⟨k, hk⟩ := htrace
  have hdet' : a*d-b*c = 64*j+1 := by omega
  have htrace' : a+d = 32*k-14 := by omega
  have square : a*a+b*c+c*b+d*d = (a+d)*(a+d)-2*(a*d-b*c) := by grind
  have form : a*a+b*c+c*b+d*d = 128*(8*k*k-7*k-j+1)+66 := by
    rw [square, hdet', htrace']
    grind
  rw [form]
  omega

/-- The formal cancellation in the mixed-pair diagram. The adjointness
and inverse are hypotheses; local and global duality supply them in the application. -/
theorem mixed_pair_cancellation {K R S D T Z : Type}
    (i : K → R) (s : S → D) (q : D → T) (jInv : T → S)
    (pairR : R → S → Z) (pairK : K → D → Z)
    (adjoint : ∀ x y, pairR (i x) y = pairK x (s y))
    (injective : ∀ a b, q a = q b → a = b)
    (rightInverse : ∀ y, q (s (jInv y)) = y) (x : K) (P : D) :
    pairR (i x) (jInv (q P)) = pairK x P := by
  rw [adjoint, injective _ _ (rightInverse (q P))]

#print axioms doubled_lift_unique
#print axioms unique_even_preimage
#print axioms doubled_lift_multiple
#print axioms doubled_lift_cocycle
#print axioms doubled_lift_additive
#print axioms doubled_lift_natural
#print axioms doubled_lift_precision
#print axioms corrected_kummer_cocycle
#print axioms matrix_square_trace
#print axioms mixed_pair_cancellation

end CentralSpecialization
