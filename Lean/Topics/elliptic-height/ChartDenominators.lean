import NumeratorEndpoint
import BadChartPrimes
import PhysicalRootCharts

namespace EllipticHeight
open PhysicalProjection.Comparison PhysicalProjection.RootOrdinate QuadraticInt ProjectionFibres.Actual
open StructuralReduction.Transfer84 ProjectionFibres
set_option maxRecDepth 8192

private theorem twice_square_integral (q : Rat) (c : Int) (eq : 2*q^2=(c:Rat)) : q=(q.num:Rat) := by
  have h : q^2=mkRat c 2 := by
    rw [Rat.mkRat_eq_div]
    have hc : (c:Rat)/2*2=(c:Rat) := Rat.div_mul_cancel (by decide)
    grobner
  have den := congrArg Rat.den h
  rw [Rat.den_pow,Rat.den_mkRat] at den
  have bound : q.den^2≤2 := by
    rw [den]
    simpa using (Nat.div_le_self 2 (Nat.gcd 2 c.natAbs))
  have d1 : q.den=1 := by
    have dp:=q.den_pos
    apply Classical.byContradiction
    intro bad
    have ge : 2≤q.den := by omega
    have four:=Nat.pow_le_pow_left ge 2
    omega
  have rep:=Rat.num_divInt_den q
  rw [Rat.divInt_eq_div,d1] at rep
  change (q.num:Rat)/1=q at rep
  simpa only [Lean.Grind.Field.div_eq_mul_inv,Lean.Grind.Field.inv_one,Rat.mul_one] using rep.symm

/-- The integral basis 1,√2 is closed under taking rational quadratic
square roots whose square has integral coordinates. -/
theorem integral_of_integral_square (z : Q2) (a : R)
    (h : PhysicalProjection.Comparison.sq z=rational a) : ∃ t : R, rational t=z := by
  let n:=PhysicalProjection.Comparison.norm z
  have nr := congrArg PhysicalProjection.Comparison.norm h
  unfold PhysicalProjection.Comparison.sq at nr
  rw [norm_product] at nr
  have nsq : 2*n^2=((2*QuadraticInt.norm a:Int):Rat) := by
    dsimp [PhysicalProjection.Comparison.norm,rational] at nr
    dsimp [n,PhysicalProjection.Comparison.norm,QuadraticInt.norm]
    simp only [Rat.intCast_mul,Rat.intCast_pow,Rat.intCast_sub] <;> grobner
  have nx:=twice_square_integral n _ nsq
  have first:=congrArg Prod.fst h
  change z.1*z.1+2*z.2*z.2=(a.1:Rat) at first
  have ne : z.1^2-2*z.2^2=(n.num:Rat) := nx
  have left:=twice_square_integral z.1 (a.1+n.num) (by rw [Rat.intCast_add];grobner)
  have right:=twice_square_integral z.2 (a.1-z.1.num^2) (by
    rw [Rat.intCast_sub,Rat.intCast_pow,←left]
    grobner)
  exact ⟨(z.1.num,z.2.num),Prod.ext left.symm right.symm⟩

private theorem quartic_identity (u j b : Q2) (h : root u j) :
    let c:=times j (PhysicalProjection.Comparison.sq b)
    let a:=times u b
    PhysicalProjection.Comparison.sq c =
      sub (PhysicalProjection.RootOrdinate.fourth a)
        (PhysicalProjection.Comparison.sq (times PhysicalProjection.Comparison.delta (PhysicalProjection.Comparison.sq b))) := by
  obtain ⟨h1,h2⟩:=(Prod.ext_iff.mp h)
  apply Prod.ext <;> dsimp [PhysicalProjection.RootOrdinate.fourth,PhysicalProjection.Comparison.sq,
    times,sub,PhysicalProjection.Comparison.delta,D2] at h1 h2 ⊢ <;> grobner

private theorem map_sq (a : R) :
    rational (QuadraticInt.sq a)=PhysicalProjection.Comparison.sq (rational a) := rational_mul a a

theorem clear_chart {u j : Q2} {a b : R} (h : root u j) (frac : represents u a b) :
    ∃ c, chart a b c := by
  let v:=mul QuadraticInt.delta (QuadraticInt.sq b)
  let f:=QuadraticInt.fourth a
  let g:=QuadraticInt.sq v
  let z:R:=(f.1-g.1,f.2-g.2)
  have kr : rational z=sub (rational f) (rational g) := by
    apply Prod.ext <;> simp [rational,z,sub,Rat.intCast_sub]
  have identity:=quartic_identity u j (rational b) h
  dsimp only at identity
  rw [frac.2] at identity
  have sqInt : PhysicalProjection.Comparison.sq (times j (PhysicalProjection.Comparison.sq (rational b)))=rational z := by
    rw [kr]
    simpa only [f,g,v,QuadraticInt.fourth,map_sq,rational_mul] using identity
  obtain ⟨c,rc⟩:=integral_of_integral_square _ z sqInt
  have ic : QuadraticInt.sq c=z := rational_injective (by rw [map_sq,rc,sqInt])
  refine ⟨c,?_⟩
  change plus (QuadraticInt.sq c) g=f
  rw [ic]
  apply Prod.ext <;> dsimp [z,plus] <;> omega

/-- Every reduced fraction for a root parameter of the stored zero has
numerator prime to √2 and 3−√2. -/
theorem actual_bad_primes (y : Fin 80→Rat) (zero : Binding.V y 9813=0) (i : Fin 4)
    {a b : R} (frac : represents (Labels.rootH (decoded y) i) a b) (pr : coprime a b) :
    divides rho b ∧ ¬divides rho a ∧ ¬divides QuadraticInt.delta a := by
  obtain ⟨rt,_,_⟩:=Labels.physical_root_charts y zero i
  obtain ⟨c,h⟩:=clear_chart rt frac
  exact ⟨dyadic_denominator h,no_dyadic_numerator pr h,no_seven_numerator pr h⟩

end EllipticHeight
#print axioms EllipticHeight.integral_of_integral_square
#print axioms EllipticHeight.clear_chart
#print axioms EllipticHeight.actual_bad_primes
