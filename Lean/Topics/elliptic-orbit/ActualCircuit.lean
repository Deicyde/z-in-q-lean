import ActualHeight
import CoprimeOrbit
import GoodCircuit

namespace EllipticOrbit
open EllipticHeight EllipticHeight.QuadraticInt
open EllipticHeight.PhysicalOrder (O)
open StructuralReduction ProjectionFibres ProjectionFibres.Actual
open ProjectionFibres.HeightSupport ProjectionFibres.Comparison HeightSpecialization
open IndependentIndices IndependentIndices.Assembly

/-- The four literal squared abscissas represent the indicated multiples of the fixed point. -/
def PhysicalLabelling {y : Fin 80 → Rat} (f : RootFractions y) (s : Labels) : Prop :=
  ∀ j, Law.Rep (D := Field.D) ((label s j).natAbs • Field.P)
    (Field.orderMap (asOrder (sq (f.a j)))) (Field.orderMap (asOrder (sq (f.b j))))

private theorem square_primitive {y : Fin 80 → Rat} (zero : Binding.V y 9813 = 0)
    (f : RootFractions y) (j : Fin 4) :
    SignedOrder.Primitive (asOrder (sq (f.a j))) (asOrder (sq (f.b j))) :=
  bezout_in_order (Primitive.physical_iterate y zero j (f.point j) (f.primitive j) 0)

private theorem rep_cross {T : Type*} [Field T] {d : T} {Q : (Law.curve d).Point}
    {a b c e : T} (p : Law.Rep Q a b) (q : Law.Rep Q c e) : a*e=b*c := by
  obtain ⟨s,_,rfl,rfl⟩ := p
  obtain ⟨t,_,rfl,rfl⟩ := q
  ring

/-- Companion parity eliminates common numerator and denominator primes at every place.
The Bézout coefficients absorb the scale of each physical representative separately. -/
theorem physical_coprime {y : Fin 80 → Rat} (zero : Binding.V y 9813 = 0)
    (f : RootFractions y) (s : Labels) (i : Fin 4) (marked : PhysicalLabelling f s)
    (odd : ∀ j, j ≠ i → label s j % 2 = 1) :
    IsCoprime (asOrder (sq (f.a i))) (∏ j : Fin 4, asOrder (sq (f.b j))) := by
  classical
  let A (j : Fin 4) := asOrder (sq (f.a j))
  let B (j : Fin 4) := asOrder (sq (f.b j))
  obtain ⟨o⟩ := exists_orbit
  have prim (k : ℕ) : IsCoprime (o.A k) (o.B k) := (o.integral k).signed.primitive k
  have whole := KummerBoundary.actual_four_coprime Field.orderMap Field.orderMap_injective
    PhysicalOrder.D Field.P o.A o.B o.rep prim PhysicalOrder.A1 PhysicalOrder.B1
    Field.generator_rep KummerBoundary.physical_seed (label s) i odd
  have scales (j : Fin 4) : ∃ t : O,
      o.A (label s j).natAbs = t * A j ∧ o.B (label s j).natAbs = t * B j := by
    apply SignedOrder.projective_scale (square_primitive zero f j)
    apply Field.orderMap_injective
    simpa only [map_mul] using rep_cross (marked j) (o.rep (label s j).natAbs)
  choose t first second using scales
  obtain ⟨u,v,bez⟩ := whole
  have product : (∏ j : Fin 4, o.B (label s j).natAbs) = (∏ j, t j) * (∏ j, B j) := by
    simp only [second, Finset.prod_mul_distrib]
  rw [first i, product] at bez
  refine ⟨u * t i, v * (∏ j, t j), ?_⟩
  change (u * t i) * A i + (v * (∏ j, t j)) * (∏ j, B j) = 1
  simpa only [mul_assoc] using bez

/-- Every stored fraction is finite, so none of its corresponding signed labels can vanish. -/
theorem label_nonzero {y : Fin 80 → Rat} {f : RootFractions y} {s : Labels}
    (marked : PhysicalLabelling f s) (j : Fin 4) : label s j ≠ 0 := by
  intro dead
  have h := marked j
  rw [dead, Int.natAbs_zero, zero_nsmul] at h
  have z := (Law.rep_zero.mp h).2
  have zo := Field.orderMap_injective (z.trans Field.orderMap.map_zero.symm)
  exact Primitive.square_nonzero (f.point j).1
    (congrArg (fun w : O => (w.re,w.im)) zo)

private theorem coprime_pair {a b : R} (h : IsCoprime (asOrder a) (asOrder b)) :
    coprime a b := by
  obtain ⟨u,v,bez⟩ := h
  refine ⟨(u.re,u.im),(v.re,v.im),?_⟩
  have e : asOrder (plus (mul a (u.re,u.im)) (mul b (v.re,v.im))) = 1 := by
    change asOrder a*u+asOrder b*v=1
    simpa only [mul_comm] using bez
  exact Prod.ext (congrArg Zsqrtd.re e) (congrArg Zsqrtd.im e)

private theorem denominator_product (b : Fin 4 → R) (i : Fin 4) :
    asOrder (mul (b i) (otherThree b i)) = ∏ j : Fin 4, asOrder (b j) := by
  have ringmap (u v : R) : asOrder (mul u v) = asOrder u * asOrder v := rfl
  fin_cases i <;> simp [Fin.prod_univ_succ,otherThree,ringmap] <;> ring

/-- The same physical numerator satisfies both the global cancellation test and the sharp bound. -/
theorem actual_factor {y : Fin 80 → Rat} (zero : Binding.V y 9813 = 0)
    (f : RootFractions y) (s : Labels) (i : Fin 4) (largest : (label s i).natAbs = labelSize s)
    (marked : PhysicalLabelling f s) (odd : ∀ j, j ≠ i → label s j % 2 = 1) :
    ∃ g : PrimitiveFactor (decoded y) s,
      (41 ^ ((label s g.row).natAbs^2))^2 ≤ (QuadraticInt.norm g.a).natAbs := by
  let a j := QuadraticInt.sq (f.a j)
  let b j := QuadraticInt.sq (f.b j)
  have rows (j) := Primitive.physical_square_representation y j (f.point j)
  have cancel : coprime (a i) (mul (b i) (otherThree b i)) := by
    apply coprime_pair
    rw [denominator_product]
    exact physical_coprime zero f s i marked odd
  let g : PrimitiveFactor (decoded y) s :=
    ⟨i,largest,a i,b i,otherThree a i,otherThree b i,rows i,rest_fraction rows i,cancel⟩
  refine ⟨g,?_⟩
  have growth := fixed_numerator (label s i).natAbs (square_primitive zero f i) (marked i)
  rw [asOrder_norm] at growth
  exact growth

/-- The selected row may have either parity in the coprimality argument.
The scalar descent uses the separate first-index parity hypothesis. -/
structure ActualSelection (y : Fin 80 → Rat) where
  labels : Labels
  row : Fin 4
  largest : (label labels row).natAbs = labelSize labels
  represented : PhysicalLabelling (reducedRoots y) labels
  companions : ∀ j, j ≠ row → label labels j % 2 = 1
  oddFirst : labels.n₁ % 2 = 1
  places : ∀ p ∈ fullPrimes (slope (decoded y) (tallest (decoded y))),
    Nonempty (SourcePlace (decoded y) (tallest (decoded y)) p labels)
  height : SlopeHeight (decoded y) (tallest (decoded y))
  offsetNonzero : labels.n₂ - 1 ≠ 0
  anchor : (anchorModulus : Int) ∣ labels.n₂ - 1
  scalar : ScalarCondition (decoded y) labels.n₂

theorem circuit_defines_of_actual_labels (marked : Bool)
    (integerFibres : ∀ n : Nat, circuitImage false (n : Rat))
    (selection : ∀ T : Rat, 0 ≤ 2*T+1 → T ≠ 0 → circuitImage false T →
      ∃ y : Fin 80 → Rat, y 0 = T ∧ Binding.V y 9813 = 0 ∧ Nonempty (ActualSelection y)) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply circuit_defines_of_one_numerator marked 41 (by decide) integerFibres
  intro T side nz represented
  obtain ⟨y,hy,hz,⟨g⟩⟩ := selection T side nz represented
  obtain ⟨factor,growth⟩ :=
    actual_factor hz (reducedRoots y) g.labels g.row g.largest g.represented g.companions
  have last : g.labels.n₄ ≠ 0 := label_nonzero g.represented 3
  let d : NumeratorData (decoded y) :=
    ⟨g.labels,g.places,factor,g.height,g.oddFirst,last,g.offsetNonzero,g.anchor⟩
  exact ⟨y,hy,hz,d,growth,g.scalar⟩

end EllipticOrbit

#print axioms EllipticOrbit.physical_coprime
#print axioms EllipticOrbit.label_nonzero
#print axioms EllipticOrbit.actual_factor
#print axioms EllipticOrbit.circuit_defines_of_actual_labels
