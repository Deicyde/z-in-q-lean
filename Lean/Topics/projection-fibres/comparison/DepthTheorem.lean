import FactorOrders
namespace ProjectionFibres.Comparison
open StructuralReduction ProgressionWitnesses.SingleContact BinaryQuartic Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

theorem coefficient_relation {N D r s t u : Rat} (hD : D≠0) (hs : s≠0) (hu : u≠0)
    (numer : N=r*u^2) (denom : D=s*t^2) : (N/D)*(t/u)^2=r/s := by
  have a:=Rat.div_mul_cancel (a:=N) hD
  have b:=Rat.div_mul_cancel (a:=t) hu
  have c:=Rat.div_mul_cancel (a:=r) hs
  have eq : ((N/D)*(t/u)^2-r/s)*(s*u^2)=0 := by
    calc _=(N/D)*(s*((t/u)*u)^2)-((r/s)*s)*u^2 := by grobner
         _=0 := by rw [b,c,←denom,a,numer];grobner
  have nz : s*u^2≠0 := fun h=>(Rat.mul_eq_zero.mp h).elim hs (by grind)
  have z:=(Rat.mul_eq_zero.mp eq).resolve_right nz
  grobner

theorem rawDepths {p : Nat} (hp : Prime p) (large : 5≤p) (away : p≠17)
    {K : Type} [Field K] (w : ExtensionPlace p K) {rho : K} (root : rho^2=2)
    (a : Data) (proper : a.valid) (b : Rat) (liveB : b≠0)
    (pole : ThreeCoordinates.Sextic (17*b) (289-17*b)) (bt : b*a.trace^2=a.R)
    (odd : OddOrder (order p a.R)) (regular : 0≤order p a.delta) :
    0<order p a.R ∧ ∃ r : K, (r=rho ∨ r= -rho) ∧
      ∀ s∈a.steps, (s.y.eval w r)≠0 → (s.m:Int)≤w.val (s.y.eval w r) := by
  obtain ⟨r0,d0,tn,td,chain,ht⟩:=proper
  have liveT : a.trace≠0:=fraction_nonzero tn td
  have rt : (-rho)^2=2 := by grobner
  obtain ⟨uW,wp,op,plus⟩:=chainOrder w hp root r0 d0 regular odd chain
  obtain ⟨_,wn,on,minus⟩:=chainOrder w hp rt r0 d0 regular odd chain
  have rel:=evaluatedTrace w rho root ht uW td
  rw [Q.eval_rational w rho _ _ td] at rel
  let va:=w.val (a.finalQ.eval w rho)
  let vb:=w.val (a.finalQ.eval w (-rho))
  have im:=w.agrees a.trace liveT
  have prod:=w.product wp wn
  have tot:=w.product im.1 prod.1
  change w.incl.map a.trace*(a.finalQ.eval w rho*a.finalQ.eval w (-rho))=_ at rel
  rw [rel,im.2,prod.2] at tot
  have lower := (toPlace w hp).add wp wn tot.1
  change min va vb≤w.val (a.finalQ.eval w rho+a.finalQ.eval w (-rho)) at lower
  rw [tot.2] at lower
  have vtrace : -max va vb≤order p a.trace := by dsimp [va,vb] at *;omega
  let v:=primeOrder p hp
  have ts:=power_order v liveT 2
  have vbrel:=v.mul _ _ liveB ts.1
  rw [bt,ts.2] at vbrel
  change order p a.R=order p b+2*order p a.trace at vbrel
  have oddB : OddOrder (order p b) := by
    obtain ⟨k,e⟩:=odd
    exact ⟨k-order p a.trace,by omega⟩
  have ib:=good_prime_positive hp large away liveB oddB pole
  have choice {r : K} (hroot : r^2=2) (sg : r=rho ∨ r= -rho)
      (win : w.val (a.finalQ.eval w r)=max va vb)
      (row : ∀ s∈a.steps, s.valid a.R a.delta ∧ (s.z.eval w r≠0 →
       w.val (a.finalQ.eval w r)≤(1-2*(2*(s.m:Int)-1))*order p a.R+2*w.val (s.z.eval w r))) :
      0<order p a.R ∧ ∃ e : K, (e=rho ∨ e= -rho) ∧
      ∀ s∈a.steps, (s.y.eval w e)≠0 → (s.m:Int)≤w.val (s.y.eval w e) := by
    obtain ⟨cz,cv⟩:=cUnit w hp large away hroot
    have nonpos : max va vb≤0 := by dsimp [va,vb];omega
    have vbEq : order p b=order p a.R-2*order p a.trace := by omega
    refine ⟨(positive_pole odd nonpos vtrace vbEq (by omega)).1,r,sg,?_⟩
    intro s sm ylive
    obtain ⟨valid,raw⟩:=row s sm
    obtain ⟨reg,z⟩:=evaluatedBound w r hroot valid.2.2.2.2.2.1 valid.2.1 valid.2.2.1
    have ord : 1≤(s.m:Int) := by have :=valid.1;omega
    have boundedDeep : deep (toPlace w hp) (2*(s.m:Int)-1) (s.z.eval w r) := by
      by_cases zz : s.z.eval w r=0
      · exact Or.inl zz
      have bd:=win ▸ raw zz
      have cap : max va vb≤min 0 ((1-2*(2*(s.m:Int)-1))*order p a.R+2*w.val (s.z.eval w r)) := by omega
      exact Or.inr (depth odd nonpos vtrace vbEq (by omega) (by omega) cap)
    rw [z] at boundedDeep
    exact ((unit_depth (toPlace w hp) cz cv reg ord).mp boundedDeep).resolve_left ylive
  by_cases comp : vb≤va
  · exact choice root (Or.inl rfl) (Int.max_eq_left comp).symm plus
  · exact choice rt (Or.inr rfl) (Int.max_eq_right (by omega)).symm minus

end ProjectionFibres.Comparison
