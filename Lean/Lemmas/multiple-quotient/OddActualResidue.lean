import ActualReciprocalDivision
import ActualAnchorBase23

/-! The odd orbit of `P` reduces to the marked 2-torsion abscissa at 3. -/
namespace Prime23.OddActual

open EllipticOrbit.Field (K D P Point ofPair coeffs ofPair_mul ofPair_coeffs coeffs_ofPair coordinates)
open ReciprocalDivision (Bits adjacent quotientPair double middle reciprocal)
open EllipticOrbit.Law (Rep curve abscissa rep_zero rep_some)
open PhysicalProjection.Comparison (Q2 times)

private abbrev KR (x : K) (r : Residues 3) := PairRed 3 (coeffs x) r
private abbrev scalar (x : K) (i : Fin 3) := KR x (i,0)

private theorem coeffs_mul (x y : K) : coeffs (x*y) = times (coeffs x) (coeffs y) := by
  rw [← coeffs_ofPair (times ..), ofPair_mul, ofPair_coeffs, ofPair_coeffs]

private theorem kmul {x y : K} {u v : Residues 3} (h : KR x u) (g : KR y v) :
    KR (x*y) (mulR u v) := by
  change PairRed 3 (coeffs (x*y)) _
  rw [coeffs_mul]
  exact h.mul g

private theorem plus_scalar {x y : K} {a b : Fin 3} (h : scalar x a) (g : scalar y b) :
    scalar (x+y) (a+b) := by
  exact ⟨h.1.add g.1, by simpa using h.2.add g.2⟩

private theorem minus_scalar {x y : K} {a b : Fin 3} (h : scalar x a) (g : scalar y b) :
    scalar (x-y) (a-b) := by
  exact ⟨by simpa [sub_eq_add_neg] using h.1.add g.1.neg,
    by simpa [sub_eq_add_neg] using h.2.add g.2.neg⟩

private theorem times_scalar {x y : K} {a b : Fin 3} (h : scalar x a) (g : scalar y b) :
    scalar (x*y) (a*b) := by simpa [mulR] using kmul h g

private abbrev slot (p : K×K) (r : Fin 3 × Fin 3) := scalar p.1 r.1 ∧ scalar p.2 r.2

private theorem double_slot {z : K} {p : K×K} {r : Fin 3 × Fin 3}
    (hz : scalar z 1) (h : slot p r) : slot (double z p) (double 1 r) := by
  have aa := times_scalar h.1 h.1
  have d := times_scalar hz (times_scalar h.2 h.2)
  have t := plus_scalar aa d
  have v := times_scalar (times_scalar h.1 h.2) (minus_scalar aa d)
  exact ⟨times_scalar t t,plus_scalar (plus_scalar v v) (plus_scalar v v)⟩

private theorem middle_slot {z : K} {p r : K×K} {u v : Fin 3 × Fin 3}
    (hz : scalar z 1) (h : slot p u) (g : slot r v) : slot (middle z p r) (middle 1 u v) := by
  have t := plus_scalar (times_scalar h.1 g.1) (times_scalar hz (times_scalar h.2 g.2))
  have w := minus_scalar (times_scalar h.1 g.2) (times_scalar g.1 h.2)
  exact ⟨times_scalar t t,times_scalar w w⟩

private theorem adjacent_slots {z : K} (hz : scalar z 1) (s : Bits) :
    slot (adjacent z s).1 (adjacent (1:Fin 3) s).1 ∧
    slot (adjacent z s).2 (adjacent (1:Fin 3) s).2 := by
  induction s with
  | zero => exact ⟨⟨pairOne,pairZero⟩,pairOne,pairOne⟩
  | bit0 s ih => exact ⟨double_slot hz ih.1,middle_slot hz ih.1 ih.2⟩
  | bit1 s ih => exact ⟨middle_slot hz ih.1 ih.2,double_slot hz ih.2⟩

private theorem parity_slots (s : Bits) : adjacent (1:Fin 3) s =
    if s.index % 2 = 0 then ((1,0),(1,1)) else ((1,1),(1,0)) := by
  induction s with
  | zero => rfl
  | bit0 s ih =>
    simp only [adjacent, ih, Bits.index, show (2 * s.index) % 2 = 0 by omega, if_true]
    split <;> decide +kernel
  | bit1 s ih =>
    simp only [adjacent, ih, Bits.index, show (2 * s.index + 1) % 2 ≠ 0 by omega, if_false]
    split <;> decide +kernel

private theorem marked_q : reciprocal (D:=D) P = ofPair Base.qP := by
  have compare (T : Point) : reciprocal (D:=D) T = ActualBase.fromCoordinates T := by
    cases T <;> simp [reciprocal, abscissa, ActualBase.fromCoordinates, coordinates]
  exact (compare P).trans ActualBase.actual_qP

private theorem qres : KR (reciprocal (D:=D) P) (0,2) := by
  change PairRed 3 (coeffs _) _
  rw [marked_q, coeffs_ofPair, Base.reciprocal_values.1]
  exact ⟨⟨456,1681,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨224,1681,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩

private theorem curve_input : scalar (D*reciprocal (D:=D) P^2) 1 := by
  rw [pow_two]
  exact kmul (x:=D) Base.curve_reduction.2.2 (kmul qres qres)

private theorem unit_live {x : K} (h : scalar x 1) : x ≠ 0 := by
  intro e
  exact (h.1.invOne (by decide)).1 (by rw [e]; rfl)

private theorem unit_inv {x : K} (h : scalar x 1) : scalar x⁻¹ 1 := by
  obtain ⟨hn,hr⟩ := h.invOne (by decide)
  have mul : x * ofPair (inverse (coeffs x)) = 1 := by
    rw [← ofPair_coeffs x, ← ofPair_mul, coeffs_ofPair, inverse_clears hn]; rfl
  have equiv : ofPair (inverse (coeffs x)) = x⁻¹ := by
    apply mul_left_cancel₀ (unit_live h)
    rw [mul, mul_inv_cancel₀ (unit_live h)]
  change PairRed 3 (coeffs x⁻¹) _
  rw [← equiv, coeffs_ofPair]
  exact hr

private theorem odd_slots {n : ℤ} (odd : n % 2 = 1) :
    let p := quotientPair (D * reciprocal (D:=D) P ^ 2) n.natAbs
    scalar p.1 1 ∧ scalar p.2 1 := by
  have odd' : n.natAbs % 2 ≠ 0 := by omega
  have h := (adjacent_slots curve_input (ReciprocalDivision.bits n.natAbs)).1
  rw [parity_slots, ReciprocalDivision.index_bits, if_neg odd'] at h
  exact h

/-- Every signed odd multiple is finite and its abscissa has coefficient residues
    `(0,1)` in the basis `1,√2` modulo 3. -/
theorem odd_abscissa (n : ℤ) (odd : n % 2 = 1) :
    ∃ x y : K, coordinates (n • P) = some (x,y) ∧ PairRed 3 (coeffs x) (0,1) := by
  let q := reciprocal (D:=D) P
  let p := quotientPair (D*q^2) n.natAbs
  obtain ⟨ha,hb⟩ : scalar p.1 1 ∧ scalar p.2 1 := odd_slots odd
  have qn : q ≠ 0 := by dsimp only [q]; rw [marked_q]; decide +kernel
  have xq : ofPair Base.xP * q = 1 := by
    dsimp only [q]
    rw [marked_q, ← ofPair_mul, Base.reciprocal_values.2.2.2.1]; rfl
  have hr : Rep (n • P) p.1 (q*p.2) :=
    ReciprocalDivision.quotient_rep P qn (ReciprocalDivision.rep_reciprocal P qn) n
  generalize n • P = T at hr ⊢
  cases T with
  | zero => exact ((mul_ne_zero qn (unit_live hb)) (rep_zero.mp hr).2).elim
  | @some x y h =>
    have eq := (rep_some h |>.mp hr).2
    have xeq : x = ofPair Base.xP * (p.1*p.2⁻¹) := by
      rw [eq]
      calc x = (ofPair Base.xP*q)*x*(p.2*p.2⁻¹) := by
               rw [xq, mul_inv_cancel₀ (unit_live hb), one_mul, mul_one]
           _ = _ := by ring
    refine ⟨x,y,rfl,?_⟩
    rw [xeq]
    exact kmul (x:=ofPair Base.xP) Base.curve_reduction.1 (times_scalar ha (unit_inv hb))

end Prime23.OddActual
