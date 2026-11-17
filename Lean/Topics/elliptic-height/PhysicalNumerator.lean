import IntegerRootBound
import ArchimedeanTriple
import QuadraticNumerator

namespace EllipticHeight
open Lean.Grind StructuralReduction StructuralReduction.Transfer84 PhysicalProjection.Comparison
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.Comparison ProjectionFibres.HeightSupport
open IndependentIndices IndependentIndices.Assembly HeightSpecialization
open QuadraticInt
set_option maxRecDepth 8192

def roots (x : Fin 84 → Rat) (i : Fin 4) : Q2 :=
  match i with
  | 0 => sq (cell x 2,cell x 3)
  | 1 => sq (atWire x 182*cell x 5,atWire x 182*cell x 6)
  | 2 => sq (cell x 7,cell x 8)
  | _ => sq (cell x 10,cell x 11)

def rest (x : Fin 84 → Rat) (i : Fin 4) : Q2 :=
  match i with
  | 0 => times (times (roots x 1) (roots x 2)) (roots x 3)
  | 1 => times (times (roots x 0) (roots x 2)) (roots x 3)
  | 2 => times (times (roots x 0) (roots x 1)) (roots x 3)
  | _ => times (times (roots x 0) (roots x 1)) (roots x 2)

abbrev coeff (x : Fin 84 → Rat) : Q2 := (atWire x 1249,atWire x 1252)

private theorem permute (a b c d : Q2) :
    let z:=times (times (times a b) c) d
    z=times a (times (times b c) d) ∧ z=times b (times (times a c) d) ∧
    z=times c (times (times a b) d) ∧ z=times d (times (times a b) c) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  all_goals apply Prod.ext <;> dsimp [times] <;> grobner

theorem split_product (x : Fin 84 → Rat) (i : Fin 4) : coeff x=times (roots x i) (rest x i) := by
  have h:=root_product x
  change coeff x=times (times (times (roots x 0) (roots x 1)) (roots x 2)) (roots x 3) at h
  rw [h]
  obtain ⟨a,b,c,d⟩:=permute (roots x 0) (roots x 1) (roots x 2) (roots x 3)
  match i with
  | 0 => exact a
  | 1 => exact b
  | 2 => exact c
  | 3 => exact d

private theorem square_norm_nonneg (a : Q2) : 0≤PhysicalProjection.Comparison.norm (sq a) := by
  unfold sq
  rw [norm_product]
  have eq (a : Rat) : a*a=a^2 := by grobner
  rw [eq]
  exact OrderedRing.sq_nonneg

private theorem norm_live (q : Q2) (h : q.1≠0) : PhysicalProjection.Comparison.norm q≠0 :=
  fun e=>h ((CircuitTransport.Quadratic.norm_zero_iff q.1 q.2).mp e).1

theorem product_norm_pos {x : Fin 84 → Rat} (dom : domain x) :
    0<PhysicalProjection.Comparison.norm (coeff x) := by
  have p:=root_product x
  change coeff x=_ at p
  have nn : 0≤PhysicalProjection.Comparison.norm (coeff x) := by
    rw [p,norm_product,norm_product,norm_product]
    exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (square_norm_nonneg _) (square_norm_nonneg _))
      (square_norm_nonneg _)) (square_norm_nonneg _)
  have nz : atWire x 1249 ≠0 := by
    intro z
    apply noMark x .second dom
    rw [(slope_values x).2.1,z]
    unfold P
    grobner
  have nzn := norm_live (coeff x) (by simpa only [coeff] using nz)
  exact Rat.lt_of_le_of_ne nn (Ne.symm nzn)

def den (x : Fin 84 → Rat) := Analytic.tripleDen (coeff x).1 (coeff x).2
def numerator (x : Fin 84 → Rat) : R :=
  (Analytic.tripleNum (den x) (coeff x).1,Analytic.tripleNum (den x) (coeff x).2)
def rational (z : R) : Q2 := ((z.1:Rat),(z.2:Rat))

private theorem scale (v : Rat) (d : Nat) (dvd : v.den∣d) :
    v*(d:Rat)=((Analytic.tripleNum d v:Int):Rat) := by
  have rep:=Rat.num_divInt_den v
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at rep
  have eq:=Analytic.scaled_coordinate (K:=Rat) v d dvd
  change ((v.num:Rat)/(v.den:Rat))*(d:Rat)=_ at eq
  rwa [rep] at eq

theorem scaled_coeff (x : Fin 84 → Rat) :
    rational (numerator x)=times ((den x:Rat),0) (coeff x) := by
  apply Prod.ext
  · simpa [rational,numerator,times,Rat.mul_comm,Rat.add_zero] using
      (scale (coeff x).1 (den x) (Nat.dvd_lcm_left ..)).symm
  · simpa [rational,numerator,times,Rat.mul_comm,Rat.add_zero] using
      (scale (coeff x).2 (den x) (Nat.dvd_lcm_right ..)).symm

private theorem finite_norm_bound (z : R) (j : Nat) (pos : 0<QuadraticInt.norm z) (cap : z.1.natAbs≤j) :
    (QuadraticInt.norm z).natAbs≤j^2 := by
  have bound : QuadraticInt.norm z≤z.1^2 := by
    have s:=Int.sq_nonnneg z.2
    unfold QuadraticInt.norm
    omega
  have ab := Int.natAbs_of_nonneg (Int.le_of_lt pos)
  have sq := Int.natAbs_of_nonneg (Int.sq_nonnneg z.1)
  rw [Int.natAbs_pow] at sq
  rw [←ab,←sq] at bound
  exact Nat.le_trans (Int.ofNat_le.mp bound) (Nat.pow_le_pow_left cap 2)

theorem numerator_norm_bound {x : Fin 84 → Rat} (dom : domain x) :
    0<QuadraticInt.norm (numerator x) ∧ (QuadraticInt.norm (numerator x)).natAbs≤(J x)^2 := by
  obtain ⟨dp,_,mJ,_⟩:=Analytic.triple_bounds (coeff x).1 (coeff x).2
  have p:=product_norm_pos dom
  have h:=congrArg PhysicalProjection.Comparison.norm (scaled_coeff x)
  rw [norm_product] at h
  have dpos : (0:Rat)<(den x:Rat) := OrderedRing.pos_natCast_of_pos _ dp
  have castNorm (a:R) : ((QuadraticInt.norm a:Int):Rat)=PhysicalProjection.Comparison.norm (rational a) := by
    simp [QuadraticInt.norm,PhysicalProjection.Comparison.norm,rational,Rat.intCast_sub,Rat.intCast_mul,Rat.intCast_pow]
  have dr : (0:Rat)<PhysicalProjection.Comparison.norm ((den x:Rat),0) := by
    have id (n : Rat) : PhysicalProjection.Comparison.norm (n,0)=n*n := by
      unfold PhysicalProjection.Comparison.norm
      grobner
    rw [id]
    exact Rat.mul_pos dpos dpos
  have pos : 0<QuadraticInt.norm (numerator x) := by
    have pp:=Rat.mul_pos dr p
    rw [←h,←castNorm] at pp
    exact (Rat.intCast_lt_intCast (a:=0)).mp pp
  refine ⟨pos,finite_norm_bound (numerator x) (J x) pos ?_⟩
  simpa only [numerator,den,coeff,J] using mJ

end EllipticHeight

#print axioms EllipticHeight.split_product
#print axioms EllipticHeight.product_norm_pos
#print axioms EllipticHeight.scaled_coeff
#print axioms EllipticHeight.numerator_norm_bound
