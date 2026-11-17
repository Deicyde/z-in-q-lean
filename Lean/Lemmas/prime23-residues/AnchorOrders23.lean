import AllMultipliers23
import InertCoordinates
import DyadicCoefficients

namespace Prime23
open Lean.Grind PhysicalProjection.Comparison StructuralReduction
attribute [local instance] Semiring.natCast Ring.intCast
variable {p : Nat} [NeZero p]

/-- An actual reduced denominator of a rational with defined residue is prime to p. -/
theorem Red.den_unit (hp : 1<p) {x : Rat} {r : Fin p} (h : Red p x r) : ¬p∣x.den := by
  obtain ⟨a,d,du,_,xe⟩:=h
  have den_nz : (x.den:Rat)≠0 := fun e=>x.den_nz (Rat.natCast_eq_zero_iff.mp e)
  have can:=Rat.num_divInt_den x
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at can
  have clear : x*(x.den:Rat)=(x.num:Rat) :=
    (congrArg (fun y:Rat=>y*(x.den:Rat)) can.symm).trans (Rat.div_mul_cancel den_nz)
  have cross : x.num*d=a*(x.den:Int) := by
    apply Rat.intCast_inj.mp
    simp only [Rat.intCast_mul,Rat.intCast_natCast]
    grobner
  have divides : (x.den:Int)∣x.num*d := by rw [cross]; exact Int.dvd_mul_left ..
  have natDiv:=Int.ofNat_dvd_left.mp divides
  rw [Int.natAbs_mul] at natDiv
  have minimal:=x.reduced.symm.dvd_of_dvd_mul_left natDiv
  intro hd
  have good : (d:Fin p)=0 := (IsCharP.intCast_eq_zero_iff p d).mpr
    (Int.dvd_iff_emod_eq_zero.mp (Int.ofNat_dvd_left.mpr (Nat.dvd_trans hd minimal)))
  rw [du] at good
  have e:=congrArg Fin.val good
  change 1%p=0 at e
  rw [Nat.mod_eq_of_lt hp] at e
  omega

theorem Red.nonneg (hp : 1<p) {x : Rat} {r : Fin p} (h : Red p x r) : 0≤order p x := by
  have den : natOrder p x.den=0 := by rw [natOrder,dif_neg (fun k=>h.den_unit hp k.2.2)]
  unfold order; rw [den]; omega

private theorem twoPrime : BinaryQuartic.Prime 2 := prime_of_finite (by decide) (by decide)
private theorem threePrime : BinaryQuartic.Prime 3 := prime_of_finite (by decide) (by decide)
private abbrev v2 := primeOrder 2 twoPrime
private abbrev v3 := primeOrder 3 threePrime

private theorem norm_scale (s : Rat) (t : Q2) : norm (scale s t)=s^2*norm t := by
  dsimp [norm,scale]; grobner

/-- Dyadic norm order on the reciprocal abscissa of a signed multiple. -/
theorem dyadic_reciprocal {q : Q2} {n : Int} (hn : n≠0)
    (h : Normalized 2 Base.qP q (n:Rat)) :
    norm q≠0 ∧ order 2 (norm q)=6+4*order 2 (n:Rat) := by
  obtain ⟨u,ur,eq⟩:=h
  have un : Red 2 (norm u) 1 := by
    simpa [Semiring.mul_zero,Semiring.mul_one,Semiring.zero_mul,AddCommGroup.neg_zero,
      AddCommMonoid.add_zero] using ur.norm
  obtain ⟨nz,uu⟩:=un.unit_order twoPrime (by decide)
  have nn : (n:Rat)≠0 := fun h=>hn (Rat.intCast_eq_zero_iff.mp h)
  obtain ⟨n2,vn2⟩:=power_order v2 nn 2
  obtain ⟨n4,vn4⟩:=power_order v2 n2 2
  have bn : norm Base.qP≠0 := by decide +kernel
  have ab : ((n:Rat)^2)^2*norm Base.qP≠0 := by grind [Rat.mul_eq_zero]
  rw [eq,norm_product,norm_scale]
  refine ⟨by grind [Rat.mul_eq_zero],?_⟩
  change v2.ord _=_
  rw [v2.mul _ _ ab nz,v2.mul _ _ n4 bn]
  have vb : v2.ord (norm Base.qP)=6 := Base.dyadic.2.1
  change v2.ord (norm u)=0 at uu
  change _=6+4*v2.ord (n:Rat)
  omega

theorem dyadic_abscissa {q x : Q2} {n : Int} (hn : n≠0) (h : Normalized 2 Base.qP q (n:Rat))
    (reciprocal : times x q=(1,0)) : order 2 (norm x)= -6-4*order 2 (n:Rat) := by
  obtain ⟨qn,qv⟩:=dyadic_reciprocal hn h
  have e:=congrArg norm reciprocal
  rw [norm_product,show norm (1,0)=1 by decide +kernel] at e
  have xn : norm x≠0 := fun z=>by rw [z,Rat.zero_mul] at e; contradiction
  have v:=congrArg (order 2) e
  change v2.ord _=v2.ord _ at v
  rw [v2.mul _ _ xn qn,v2.one] at v
  change v2.ord (norm q)=6+4*v2.ord (n:Rat) at qv
  change v2.ord (norm x)= -6-4*v2.ord (n:Rat)
  omega

theorem dyadic_root {q g : Q2} {n : Int} (hn : n≠0) (h : Normalized 2 Base.qP q (n:Rat))
    (root : sq g=q) : (¬2∣g.1.den) ∧ (¬2∣g.2.den) := by
  obtain ⟨qn,qv⟩:=dyadic_reciprocal hn h
  change times g g=q at root
  have e:=congrArg norm root
  rw [norm_product] at e
  have gn : norm g≠0 := fun z=>qn (by rw [←e,z,Rat.zero_mul])
  have v:=congrArg (order 2) e
  change v2.ord _=v2.ord _ at v
  rw [v2.mul _ _ gn gn] at v
  have ni : 0≤order 2 (n:Rat) := by rw [order_int twoPrime]; omega
  change order 2 (norm g)+order 2 (norm g)=order 2 (norm q) at v
  exact AnchorCollision.Dyadic.odd_den_coordinates
    ((AnchorCollision.Dyadic.integral_iff_odd_den _).mp (by omega))

/-- Both rational coordinates of the translated reciprocal square root have
order 1+v₃(n) when it lies over [2n]P. -/
theorem triadic_root {q g : Q2} {n : Int} (hn : n≠0) (h : Normalized 3 Base.qDouble q (n:Rat))
    (root : sq g=q) :
    g.1≠0 ∧ g.2≠0 ∧ order 3 g.1=1+order 3 (n:Rat) ∧ order 3 g.2=1+order 3 (n:Rat) := by
  obtain ⟨u,ur,ue⟩:=h
  have seed : Base.qDouble=scale 9 (scale (1/9) Base.qDouble) := by decide +kernel
  obtain ⟨t,tr,te⟩:=normalized_output seed Base.triadic.2.1 ue ur
  have nn : (n:Rat)≠0 := fun e=>hn (Rat.intCast_eq_zero_iff.mp e)
  obtain ⟨n2,on⟩:=power_order v3 nn 2
  have dep : (n:Rat)^2*9≠0 := by grind [Rat.mul_eq_zero]
  have nine : v3.ord 9=2 := by decide +kernel
  have val : order 3 ((n:Rat)^2*9)=2*(1+order 3 (n:Rat)) := by
    change v3.ord _=2*(1+v3.ord _)
    rw [v3.mul _ _ n2 (by decide),nine]; omega
  obtain ⟨im,iv⟩:=tr.2.unit_order threePrime (by decide)
  have av:=tr.1.nonneg (by decide)
  have hx:=congrArg Prod.fst (root.trans te)
  have hy:=congrArg Prod.snd (root.trans te)
  change g.1*g.1+2*g.2*g.2=((n:Rat)^2*9)*t.1 at hx
  change g.1*g.2+g.2*g.1=((n:Rat)^2*9)*t.2 at hy
  have re : g.1^2+2*g.2^2=((n:Rat)^2*9)*t.1 := by grobner
  have ie : 2*g.1*g.2=((n:Rat)^2*9)*t.2 := by grobner
  apply AnchorCircuit.Inert.three_adic_coordinates
  · rw [re]
    by_cases tz : t.1=0
    · exact Or.inl (by rw [tz,Rat.mul_zero])
    · apply Or.inr
      have dis : order 3 (((n:Rat)^2*9)*t.1)=order 3 ((n:Rat)^2*9)+order 3 t.1 := v3.mul _ _ dep tz
      omega
  · rw [ie]; exact fun z=>(Rat.mul_eq_zero.mp z).elim dep im
  · rw [ie]
    have dis : order 3 (((n:Rat)^2*9)*t.2)=order 3 ((n:Rat)^2*9)+order 3 t.2 := v3.mul _ _ dep im
    omega

theorem odd_product {a b c d : Q2}
    (ha : PairRed 3 a (0,1)) (hb : PairRed 3 b (0,1)) (hc : PairRed 3 c (0,1)) (hd : PairRed 3 d (0,1)) :
    let t:=times (times (times a b) c) d
    PairRed 3 t (1,0) ∧ (¬3∣t.1.den) := by
  have r:=((ha.mul hb).mul hc).mul hd
  change PairRed 3 _ (1,0) at r
  exact ⟨r,r.1.den_unit (by decide)⟩

#print axioms dyadic_abscissa
#print axioms dyadic_root
#print axioms triadic_root
#print axioms odd_product
end Prime23
