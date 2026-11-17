import AbscissaClass
import OrbitClasses
import SignedDoubles
import PhysicalRootCharts

namespace EllipticOrbit.SignedLabels
open EllipticOrbit.Field
open EllipticOrbit.AbscissaClass
open PhysicalProjection.Comparison (Q2)
open PhysicalProjection.RootOrdinate (root)

private theorem zero_root : E.toAffine.Nonsingular 0 0 := by
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular (W:=E)).mp
  rw [equation]
  ring

private theorem delta_root : E.toAffine.Nonsingular delta 0 := by
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular (W:=E)).mp
  rw [equation,←delta_sq]
  ring

def T : Point := .some zero_root
def U : Point := .some delta_root

/-- The part of the native Mordell--Weil calculation needed to recover labels. -/
def Generated : Prop := ∀ Q : Point, ∃ (m : ℤ) (a d : Bool),
  Q=m • R+(if a then T else 0)+(if d then U else 0)

private def signed (e : Bool) (A : Point) : Point := if e then A else 0
private def bit (e : Bool) (a : K) : K := if e then a else 1

private theorem value_R : value (D:=D) R=xR := by
  change finiteValue D xR=xR
  simp [finiteValue,show xR≠0 by decide]

private theorem value_T : value (D:=D) T= -D := by simp [T,value,finiteValue]
private theorem value_U : value (D:=D) U=delta := by
  change finiteValue D delta=delta
  simp [finiteValue,show delta≠0 by decide]

private theorem signed_R (e : Bool) : Same (value (D:=D) (signed e R)) (bit e xR) := by
  cases e
  · exact Same.refl 1
  · simpa [signed,bit,value_R] using Same.refl xR

private theorem signed_T (a : Bool) : Same (value (D:=D) (signed a T)) (bit a (-1)) := by
  cases a
  · exact Same.refl 1
  · refine ⟨delta,by decide,?_⟩
    change value (D:=D) T= -1*delta^2
    rw [value_T,delta_sq,neg_one_mul]

private theorem signed_U (d : Bool) : Same (value (D:=D) (signed d U)) (bit d delta) := by
  cases d
  · exact Same.refl 1
  · simpa [signed,bit,value_U] using Same.refl delta

private theorem constant_classes (a d e : Bool) : bit e xR*bit a (-1)*bit d delta =
    ofPair (OrbitIdentification.representative a d e) := by
  cases a <;> cases d <;> cases e <;> ext <;>
    norm_num [bit,xR,delta,ofPair,OrbitIdentification.representative,OrbitIdentification.times,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

private theorem decomposition_class (k : ℤ) (a d e : Bool) :
    Same (value (D:=D) ((2:ℤ) • (k • R)+signed e R+signed a T+signed d U))
      (ofPair (OrbitIdentification.representative a d e)) := by
  have double:=value_double (D:=D) D_ne_zero (k • R)
  have p:=(value_add (D:=D) D_ne_zero ((2:ℤ) • (k • R)) (signed e R)).trans (double.mul (signed_R e))
  have q:=(value_add (D:=D) D_ne_zero _ (signed a T)).trans (p.mul (signed_T a))
  have r:=(value_add (D:=D) D_ne_zero _ (signed d U)).trans (q.mul (signed_U d))
  simpa only [one_mul,constant_classes] using r

private theorem norm_unit {z : K} (nz : z≠0) : OrbitIdentification.norm (coeffs z)≠0 := by
  intro zero
  have e:=(CircuitTransport.Quadratic.norm_zero_iff z.re z.im).mp zero
  exact nz (by ext <;> simp [e.1,e.2])

/-- A point of the actual group whose class is represented by a nonzero
    square has an integer index on the doubled marked generator. -/
theorem square_multiple (group : Generated) (Q : Point) (h : Q2)
    (sq : value (D:=D) Q=(ofPair h)^2) : ∃ k : ℤ, Q=k • P := by
  obtain ⟨m,a,d,eq⟩:=group Q
  let k:=m/2
  let e:=decide (m%2=1)
  let rem : ℤ := if e then 1 else 0
  have mod : m=2*k+rem := by
    by_cases odd : m%2=1 <;> simp [rem,e,k,odd] <;> omega
  have er : rem • R=signed e R := by
    unfold rem signed
    cases e <;> simp
  have coord : Q=(2:ℤ) • (k • R)+signed e R+signed a T+signed d U := by
    conv => lhs; rw [eq,mod,add_zsmul,mul_zsmul,er]
    rfl
  obtain ⟨z,nz,c⟩:=decomposition_class k a d e
  rw [←coord,sq] at c
  have pp : OrbitIdentification.sq h=OrbitIdentification.times
      (OrbitIdentification.representative a d e) (OrbitIdentification.sq (coeffs z)) := by
    apply ofPair_injective
    change ofPair (PhysicalProjection.Comparison.sq h)=
      ofPair (PhysicalProjection.Comparison.times _ (PhysicalProjection.Comparison.sq _))
    simpa only [ofPair_mul,ofPair_sq,ofPair_coeffs] using c
  obtain ⟨ha,hd,he⟩:=OrbitIdentification.class_of_square a d e h (coeffs z) (norm_unit nz) pp
  refine ⟨k,?_⟩
  rw [coord,ha,hd,he]
  simp [signed,P,two_zsmul,two_nsmul,zsmul_add]

/-- The recovered integer indexes the actual signed point, including its ordinate. -/
theorem chart_label (group : Generated) {h j : Q2} (chart : root h j) :
    ∃ n : ℤ, n≠0 ∧ chartPoint chart=n • P := by
  have nz : ofPair h≠0 := by
    intro z
    exact (PhysicalProjection.RootOrdinate.root_nonzero chart) (ofPair_injective z)
  obtain ⟨n,hn⟩:=square_multiple group (chartPoint chart) h
    (by change finiteValue D ((ofPair h)^2)=(ofPair h)^2; simp [finiteValue,pow_ne_zero 2 nz])
  refine ⟨n,?_,hn⟩
  rintro rfl
  rw [zero_zsmul] at hn
  cases hn

open ProjectionFibres ProjectionFibres.Actual EllipticHeight.Labels

/-- Each literal signed root at an ordinary zero of the eighty-coordinate circuit
    is a nonzero integer multiple of P, under the single group generation statement. -/
theorem physical_labels (group : Generated) (y : Fin 80 → Rat) (zero : Binding.V y 9813=0) :
    ∃ n : Fin 4 → ℤ, ∀ i, n i≠0 ∧
      chartPoint (physical_root_charts y zero i).1=n i • P := by
  choose n hn he using fun i=>chart_label group (physical_root_charts y zero i).1
  exact ⟨n,fun i=>⟨hn i,he i⟩⟩

end EllipticOrbit.SignedLabels

#print axioms EllipticOrbit.SignedLabels.square_multiple
#print axioms EllipticOrbit.SignedLabels.chart_label
#print axioms EllipticOrbit.SignedLabels.physical_labels
