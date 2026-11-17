import SharpCircuit
import FractionProducts
import PhysicalPrimitive
import GoodDenominator
import ReducedFractions

namespace EllipticHeight
open QuadraticInt PhysicalOrder StructuralReduction ProjectionFibres ProjectionFibres.Actual
open ProjectionFibres.HeightSupport ProjectionFibres.Comparison HeightSpecialization
open IndependentIndices IndependentIndices.Assembly

/-- Reduced fractions for the four literal root parameters. -/
structure RootFractions (y : Fin 80 → Rat) where
  a : Fin 4 → R
  b : Fin 4 → R
  point : ∀ i, represents (Labels.rootH (decoded y) i) (a i) (b i)
  primitive : ∀ i, coprime (a i) (b i)

/-- A reduced representative exists for every rational coefficient pair. -/
noncomputable def reducedRoots (y : Fin 80 → Rat) : RootFractions y := by
  let s (i : Fin 4):=Reduction.reduced_fraction (Labels.rootH (decoded y) i)
  let t (i : Fin 4):=Classical.choose_spec (s i)
  exact ⟨fun i=>Classical.choose (s i),fun i=>Classical.choose (t i),
    fun i=>(Classical.choose_spec (t i)).1,fun i=>(Classical.choose_spec (t i)).2⟩

def GoodReductionRows {y : Fin 80 → Rat} (f : RootFractions y) (s : Labels) (i : Fin 4) : Prop :=
  ∀ (M : Ideal O) (j : Fin 4), M.IsMaximal → asOrder rho ∉ M → asOrder QuadraticInt.delta ∉ M →
    asOrder (QuadraticInt.sq (f.a i)) ∈ M → asOrder (QuadraticInt.sq (f.b j)) ∈ M →
    ∃ (G : AddGrpCat.{0}) (P T : G), T≠0 ∧ (2:ℤ) • T=0 ∧
      label s i • P=T ∧ label s j • P=0

private theorem coprime_back {a b : R} (h : IsCoprime (asOrder a) (asOrder b)) : coprime a b := by
  obtain ⟨u,v,bez⟩:=h
  refine ⟨(u.re,u.im),(v.re,v.im),?_⟩
  have e : asOrder (plus (mul a (u.re,u.im)) (mul b (v.re,v.im))) = 1 := by
    change asOrder a*u+asOrder b*v=1
    simpa only [mul_comm] using bez
  exact Prod.ext (congrArg Zsqrtd.re e) (congrArg Zsqrtd.im e)

private theorem all_denominators (b : Fin 4 → R) (i : Fin 4) :
    asOrder (mul (b i) (otherThree b i))=∏ j : Fin 4, asOrder (b j) := by
  have ringmap (u v : R) : asOrder (mul u v) = asOrder u * asOrder v := rfl
  fin_cases i <;> simp [Fin.prod_univ_succ,otherThree,ringmap] <;> ring

def factor_at_good_places (y : Fin 80 → Rat) (zero : Binding.V y 9813=0)
    (f : RootFractions y) (s : Labels) (i : Fin 4) (largest : (label s i).natAbs=labelSize s)
    (odd : ∀ j, j≠i → label s j%2=1) (good : GoodReductionRows f s i) : PrimitiveFactor (decoded y) s := by
  let a j:=QuadraticInt.sq (f.a j)
  let b j:=QuadraticInt.sq (f.b j)
  have rows (j) := Primitive.physical_square_representation y j (f.point j)
  refine {row:=i,largest:=largest,a:=a i,b:=b i,e:=otherThree a i,f:=otherThree b i,
          point:=rows i,others:=rest_fraction rows i,primeToDenominator:=?_}
  obtain ⟨h,_,_⟩:=Labels.physical_root_charts y zero i
  obtain ⟨c,hc⟩:=clear_chart h (f.point i)
  obtain ⟨atTwo,atSeven⟩:=exceptional_coprime (f.primitive i) hc
  apply coprime_back
  rw [all_denominators]
  exact numerator_coprime_denominators (asOrder (a i)) (asOrder rho) (asOrder QuadraticInt.delta)
    (fun j=>asOrder (b j)) (label s) i (bezout_in_order atTwo) (bezout_in_order atSeven) odd good

/-- Shared labels, their geometric interpretation, and the earlier selected
local tests suffice. All numerator height and cancellation estimates follow. -/
structure GeometricSelection (y : Fin 80 → Rat) where
  labels : Labels
  row : Fin 4
  largest : (label labels row).natAbs=labelSize labels
  odd : ∀ i, label labels i%2=1
  good : GoodReductionRows (reducedRoots y) labels row
  orbit : ∃ A B : ℕ → O, IntegralOrbit A B (label labels row).natAbs ∧
    A (label labels row).natAbs=asOrder (QuadraticInt.sq ((reducedRoots y).a row))
  places : ∀ p∈fullPrimes (slope (decoded y) (tallest (decoded y))),
    Nonempty (SourcePlace (decoded y) (tallest (decoded y)) p labels)
  height : SlopeHeight (decoded y) (tallest (decoded y))
  offsetNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int)∣labels.n₂-1
  scalar : ScalarCondition (decoded y) labels.n₂

theorem circuit_defines_of_signed_geometry (marked : Bool)
    (integerFibres : ∀ n : Nat, circuitImage false (n:Rat))
    (selection : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ Binding.V y 9813=0 ∧ Nonempty (GeometricSelection y)) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply circuit_defines_of_quadratic_order marked integerFibres
  intro T side nz represented
  obtain ⟨y,hy,hz,⟨g⟩⟩:=selection T side nz represented
  let f:=factor_at_good_places y hz (reducedRoots y) g.labels g.row g.largest (fun j _=>g.odd j) g.good
  have last : g.labels.n₄≠0 := by
    have h:=g.odd 3
    change g.labels.n₄%2=1 at h
    omega
  let data : NumeratorData (decoded y):=⟨g.labels,g.places,f,g.height,g.odd 0,last,g.offsetNonzero,g.anchor⟩
  exact ⟨y,hy,hz,data,g.orbit,g.scalar⟩

end EllipticHeight
#print axioms EllipticHeight.factor_at_good_places
#print axioms EllipticHeight.circuit_defines_of_signed_geometry
