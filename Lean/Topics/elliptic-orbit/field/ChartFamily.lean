import KummerLaw
import SignedDoubles
import ReducedFractions

namespace EllipticOrbit.Field
open EllipticHeight.QuadraticInt

private theorem squared_order_map (a : EllipticHeight.QuadraticInt.R) :
    orderMap (asOrder (sq a))=(orderMap (asOrder a))^2 := by
  change orderMap (asOrder a*asOrder a)=_
  rw [map_mul,pow_two]

private theorem finite_chart_rep {h j : PhysicalProjection.Comparison.Q2}
    (signed : PhysicalProjection.RootOrdinate.root h j) :
    ∃ a b c : EllipticHeight.QuadraticInt.R, coprime a b ∧ chart a b c ∧
      EllipticOrbit.Law.Rep (D:=D) (chartPoint signed)
        (orderMap (asOrder (sq a))) (orderMap (asOrder (sq b))) := by
  obtain ⟨a,b,c,frac,pr,weighted,_⟩:=EllipticHeight.Reduction.signed_chart_fraction signed
  have cross:=(fraction_iff h a b).mp frac.2
  have nonzero : orderMap (asOrder b)≠0 := by
    intro hb
    have o:=orderMap_injective (hb.trans orderMap.map_zero.symm)
    exact frac.1 (congrArg (fun p : O=>(p.re,p.im)) o)
  refine ⟨a,b,c,pr,weighted,?_⟩
  apply (EllipticOrbit.Law.rep_some (quartic_nonsingular signed)).mpr
  rw [squared_order_map,squared_order_map,←cross,mul_pow]
  exact ⟨pow_ne_zero 2 nonzero,rfl⟩

private theorem infinity_chart_rep :
    coprime (1,0) (0,0) ∧ chart (1,0) (0,0) (1,0) ∧
      EllipticOrbit.Law.Rep (D:=D) (0:Point)
        (orderMap (asOrder (sq (1,0)))) (orderMap (asOrder (sq (0,0)))) := by
  refine ⟨⟨(1,0),(0,0),by decide⟩,by unfold chart; decide,EllipticOrbit.Law.rep_zero.mpr ?_⟩
  change (1:K)≠0 ∧ (0:K)=0
  exact ⟨one_ne_zero,rfl⟩

/-- The projective generator pair used in the sharp height recurrence. -/
theorem generator_rep :
    EllipticOrbit.Law.Rep (D:=D) P (orderMap (⟨57,-28⟩:O)) (orderMap (8:O)) := by
  have data:=P_pair
  generalize point : P=Q at data ⊢
  cases Q with
  | zero => cases data
  | @some x y nonsing =>
    have hx:=congrArg Prod.fst (Option.some.inj data)
    apply (EllipticOrbit.Law.rep_some nonsing).mpr
    constructor
    · rw [map_ofNat]; norm_num
    · change x=ofPair (57/8,-7/2) at hx
      rw [hx,map_ofNat]
      ext <;> norm_num [orderMap,ofPair,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

/-- The actual cyclic orbit has primitive integral weighted charts at every
natural index. Infinity uses a=1, b=0, c=1. -/
theorem chart_family (n : ℕ) :
    ∃ a b c : EllipticHeight.QuadraticInt.R, coprime a b ∧ chart a b c ∧
      EllipticOrbit.Law.Rep (D:=D) (n • P)
        (orderMap (asOrder (sq a))) (orderMap (asOrder (sq b))) := by
  rcases nsmul_P_signed n with infinity|⟨h,j,signed,point⟩
  · rw [infinity]
    exact ⟨(1,0),(0,0),(1,0),infinity_chart_rep⟩
  · rw [point]
    exact finite_chart_rep signed

theorem signed_chart_family (n : ℤ) :
    ∃ a b c : EllipticHeight.QuadraticInt.R, coprime a b ∧ chart a b c ∧
      EllipticOrbit.Law.Rep (D:=D) (n • P)
        (orderMap (asOrder (sq a))) (orderMap (asOrder (sq b))) := by
  rcases zsmul_P_signed n with infinity|⟨h,j,signed,point⟩
  · rw [infinity]
    exact ⟨(1,0),(0,0),(1,0),infinity_chart_rep⟩
  · rw [point]
    exact finite_chart_rep signed

#print axioms chart_family
#print axioms signed_chart_family
#print axioms generator_rep
end EllipticOrbit.Field
