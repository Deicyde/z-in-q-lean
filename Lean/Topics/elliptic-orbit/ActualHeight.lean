import ChartFamily
import ChartedOrbit

namespace EllipticOrbit
open EllipticHeight
open EllipticHeight.PhysicalOrder (O A1 B1)

private theorem same_cross {T : Type*} [Field T] {d : T} {Q : (Law.curve d).Point}
    {a b c e : T} (p : Law.Rep Q a b) (q : Law.Rep Q c e) : a*e=b*c := by
  obtain ⟨s,_,rfl,rfl⟩:=p
  obtain ⟨t,_,rfl,rfl⟩:=q
  ring

structure Orbit where
  A : ℕ → O
  B : ℕ → O
  charts : ∀ i, ∃ a b c : QuadraticInt.R, QuadraticInt.coprime a b ∧ QuadraticInt.chart a b c ∧
    A i = asOrder (QuadraticInt.sq a) ∧ B i = asOrder (QuadraticInt.sq b)
  rep : ∀ i, Law.Rep (D:=Field.D) (i • Field.P) (Field.orderMap (A i)) (Field.orderMap (B i))

theorem exists_orbit : Nonempty Orbit := by
  classical
  choose a b c prim chart rep using Field.chart_family
  exact ⟨⟨fun i=>asOrder (QuadraticInt.sq (a i)),fun i=>asOrder (QuadraticInt.sq (b i)),
       fun i=>⟨a i,b i,c i,prim i,chart i,rfl,rfl⟩,rep⟩⟩

theorem Orbit.integral (o : Orbit) (n : ℕ) : IntegralOrbit o.A o.B n := by
  have d : Field.orderMap PhysicalOrder.D = Field.D := by decide
  refine ⟨o.charts,?_,?_,?_,?_⟩
  · apply Field.orderMap_injective
    rw [map_zero]
    have h0 : Law.Rep (D:=Field.D) (0:Field.Point)
        (Field.orderMap (o.A 0)) (Field.orderMap (o.B 0)) := by
      simpa only [zero_nsmul] using o.rep 0
    exact (Law.rep_zero.mp h0).2
  · apply Field.orderMap_injective
    simp only [map_mul]
    apply same_cross _ Field.generator_rep
    simpa only [one_nsmul] using o.rep 1
  · exact Law.orbit_double_cross_of_map Field.orderMap Field.orderMap_injective d Field.P
      o.A o.B o.rep
  · intro j _
    exact Law.orbit_symmetric_cross_of_map Field.orderMap Field.orderMap_injective d Field.P
      o.A o.B o.rep j

/-- The sharp bound for any primitive projective coordinates of the actual multiple. -/
theorem fixed_numerator (n : ℕ) {a b : O} (p : SignedOrder.Primitive a b)
    (h : Law.Rep (D:=Field.D) (n • Field.P) (Field.orderMap a) (Field.orderMap b)) :
    (41^(n^2))^2 ≤ a.norm.natAbs := by
  obtain ⟨o⟩ := exists_orbit
  have t:=o.integral n
  have eq : o.A n*b=o.B n*a := by
    apply Field.orderMap_injective
    simpa only [map_mul] using same_cross (o.rep n) h
  have mass:=SignedOrder.projective_mass PhysicalOrder.realNorm (t.signed.primitive n) p eq
  change (o.A n).norm.natAbs=a.norm.natAbs at mass
  exact (t.bound).trans_eq mass

/-- Infinite order follows at once by testing the primitive coordinates [1:0]. -/
theorem no_positive_multiple_zero (n : ℕ) (hn : n≠0) : n • Field.P≠0 := by
  intro zero
  have r : Law.Rep (D:=Field.D) (n • Field.P) (Field.orderMap 1) (Field.orderMap 0) := by
    rw [zero,map_zero,map_one]
    exact Law.rep_zero.mpr ⟨one_ne_zero,rfl⟩
  have bad:=fixed_numerator n (a:=1) (b:=0) ⟨1,0,by ring⟩ r
  change (41^(n^2))^2 ≤ 1 at bad
  have gt : 1 < (41:ℕ)^(n^2) := one_lt_pow₀ (by decide) (pow_ne_zero 2 hn)
  nlinarith

end EllipticOrbit
#print axioms EllipticOrbit.exists_orbit
#print axioms EllipticOrbit.Orbit.integral
#print axioms EllipticOrbit.fixed_numerator
#print axioms EllipticOrbit.no_positive_multiple_zero
