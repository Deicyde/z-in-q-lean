import Coefficients
import ActualReciprocalDivision
import ActualGenerator
import GuardedMultipliers23

/-! The integral-polynomial computation at 2 and 3 on the signed multiples
of an actual point of the quadratic elliptic curve. -/
namespace Prime23.Actual
open PhysicalProjection.Comparison (Q2 times sq)
open EllipticOrbit.Field (K D P Point ofPair coeffs ofPair_mul ofPair_sq ofPair_coeffs
  coeffs_ofPair ofPair_injective)
open ReciprocalDivision (reciprocal quotientPair)
open ReciprocalDivision.Coefficients (topTail bottomTail table_eval)

def orbit (S : Point) (n : ℤ) : Q2 := coeffs (reciprocal (D:=D) (n • S))

theorem map_eval (z : Q2) (a : List ℤ) :
    ofPair (Prime23.eval a z)=ReciprocalDivision.Coefficients.eval (ofPair z) a := by
  induction a with
  | nil => rfl
  | cons k a ih =>
    change ofPair ((k:ℚ),0)+ofPair (times z (Prime23.eval a z))=_
    rw [ofPair_mul,ih]
    change (⟨(k:ℚ),0⟩:K)+_= (k:K)+_
    congr 1

private theorem input_eq (S : Point) (i : ℤ) :
    ofPair (orbit S i)=reciprocal (D:=D) (i • S) := rfl

private theorem top_nonzero {p : ℕ} [NeZero p] (hp : 1<p) {q : Q2}
    (hq : PairRed p q (0,0)) (m : ℤ) :
    (quotientPair (D*(ofPair q)^2) m.natAbs).1≠0 := by
  let z:=times Base.D (sq q)
  have zr : PairRed p z (0,0) := by
    have zy := (hq.zero_mul ⟨_,hq⟩).zero_mul (baseD_integral p)
    change PairRed p (times (sq q) Base.D) (0,0) at zy
    have comm : times (sq q) Base.D=times Base.D (sq q) := by
      apply ofPair_injective; rw [ofPair_mul,ofPair_mul,mul_comm]
    rw [comm] at zy
    exact zy
  have unit : PairRed p (Prime23.eval (1::topTail m) z) (1,0) :=
    (zr.zero_mul (eval_integral _ ⟨_,zr⟩)).one_plus
  have zn : ofPair z=D*(ofPair q)^2 := (ofPair_mul ..).trans (by rw [ofPair_sq]; rfl)
  have te := congrArg Prod.fst (table_eval (ofPair z) m)
  change ReciprocalDivision.Coefficients.eval _ _=_ at te
  rw [←map_eval,zn] at te
  intro h
  rw [←te] at h
  have hz : Prime23.eval (1::topTail m) z=(0,0) := congrArg coeffs h
  exact (unit.1.invOne hp).1 (congrArg Prod.fst hz)

/-- On the residue disc the top projective coordinate reduces to one. Hence the
cleared multiplication equation applies without an assumption on the output. -/
theorem orbit_guarded {p : ℕ} [NeZero p] (hp : 1<p) (S : Point) :
    GuardedValues p Base.D (orbit S) topTail bottomTail := by
  intro i m _ _ hn hr
  have nz : reciprocal (D:=D) (i • S)≠0 := by
    intro h
    exact hn (congrArg coeffs h)
  have top := top_nonzero hp hr m
  rw [input_eq] at top
  have geo := ReciprocalDivision.total_reciprocal_equation (D:=D) (i • S) nz m top
  have idx : m • (i • S)=(i*m) • S := by rw [← mul_zsmul,mul_comm]
  rw [idx] at geo
  let z:=times Base.D (sq (orbit S i))
  have ze : ofPair z=D*reciprocal (D:=D) (i • S)^2 := by
    rw [ofPair_mul,ofPair_sq,input_eq]; rfl
  have t := table_eval (ofPair z) m
  apply ofPair_injective
  change ofPair (times (orbit S (i*m)) (Prime23.eval (1::topTail m) z))=
    ofPair (times (orbit S i) (Prime23.eval ((m*m)::bottomTail m) z))
  rw [ofPair_mul,ofPair_mul,map_eval,map_eval,input_eq,input_eq]
  rw [show ReciprocalDivision.Coefficients.eval (ofPair z) (1::topTail m)=_ from congrArg Prod.fst t,
      show ReciprocalDivision.Coefficients.eval (ofPair z) ((m*m)::bottomTail m)=_ from congrArg Prod.snd t,ze]
  exact geo

#print axioms orbit_guarded
end Prime23.Actual
