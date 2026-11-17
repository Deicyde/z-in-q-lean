import ActualDepths

namespace ComparisonBudget
open ProjectionFibres.Comparison StructuralReduction StructuralReduction.Transfer84
open BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
variable {p : Nat} {K : Type} [Field K]

/-- The loss of valuation due to one factor, including an exactly zero test. -/
noncomputable def loss (w : ExtensionPlace p K) (r : K) (R δ : Rat) (s : Step) : Int := by
  classical
  exact if s.z.eval w r=0 then 0 else
    max 0 ((4*(s.m:Int)-3)*order p R+4*(s.m:Int)*order p δ-2*w.val (s.z.eval w r))

private theorem oneOrder (w : ExtensionPlace p K) (hp : Prime p) : w.val 1=0 := by
  have h := (w.agrees 1 (by decide)).2
  rw [w.incl.one] at h
  exact h.trans (primeOrder p hp).one

private theorem factorOrder (w : ExtensionPlace p K) (hp : Prime p)
    (r : K) (root : r^2=2) {R δ : Rat} (nz : R≠0) (dn : δ≠0) (odd : OddOrder (order p R))
    (s : Step) (valid : s.valid R δ) :
    s.factor.eval w r≠0 ∧ w.val (s.factor.eval w r) = -loss w r R δ s := by
  classical
  have whole:=valid
  obtain ⟨_,_,uz,uq,uf,_,hf,_⟩:=valid
  have f:=evaluatedFactor w r root hf uz uq uf
  rw [Q.eval_rational w r _ _ uq] at f
  change _=1+w.incl.map s.weight*(s.z.eval w r*s.z.eval w r) at f
  have oneK : (1:K)≠0 := Ne.symm Field.zero_ne_one
  by_cases zz : s.z.eval w r=0
  · rw [zz,Semiring.mul_zero,Semiring.mul_zero,AddCommMonoid.add_zero] at f
    rw [f,loss,if_pos zz,oneOrder w hp]
    exact ⟨oneK,rfl⟩
  obtain ⟨q0,qv⟩:=weightOrder hp nz dn whole
  have im:=w.agrees s.weight q0
  have sq:=w.product zz zz
  have term:=w.product im.1 sq.1
  rw [im.2,sq.2,qv] at term
  obtain ⟨j,hj⟩:=odd
  have parity :
      (3-4*(s.m:Int))*order p R-4*(s.m:Int)*order p δ+
      (w.val (s.z.eval w r)+w.val (s.z.eval w r)) =
      2*(3*j+1-2*(s.m:Int)*order p R-2*(s.m:Int)*order p δ+w.val (s.z.eval w r))+1 := by
    rw [hj];grobner
  have diff : w.val (1:K)≠w.val (w.incl.map s.weight*(s.z.eval w r*s.z.eval w r)) := by
    rw [oneOrder w hp,term.2,parity];omega
  have h:=w.addUnequal _ _ oneK term.1 diff
  rw [←f,oneOrder w hp,term.2] at h
  refine ⟨h.1,?_⟩
  rw [h.2,loss,if_neg zz]
  have flip :
      (3-4*(s.m:Int))*order p R-4*(s.m:Int)*order p δ+
      (w.val (s.z.eval w r)+w.val (s.z.eval w r)) =
      -((4*(s.m:Int)-3)*order p R+4*(s.m:Int)*order p δ-2*w.val (s.z.eval w r)) := by grobner
  rw [flip];omega

private theorem chainOrderExact (w : ExtensionPlace p K) (hp : Prime p)
    (r : K) (root : r^2=2) {R δ : Rat} (nz : R≠0) (dn : δ≠0) (odd : OddOrder (order p R))
    {ss W} (chain : Chain R δ ss W) :
    W.d≠0 ∧ W.eval w r≠0 ∧ w.val (W.eval w r) = -(ss.map (loss w r R δ)).sum := by
  induction chain with
  | nil =>
    refine ⟨by decide,?_,?_⟩
    · rw [eval_one];exact Ne.symm Field.zero_ne_one
    · rw [eval_one,oneOrder w hp];rfl
  | add old s after valid safe prod ih =>
    obtain ⟨preSafe,pre0,preOrder⟩:=ih
    obtain ⟨f0,fo⟩:=factorOrder w hp r root nz dn odd s valid
    have eq:=evaluatedProduct w r root prod preSafe valid.2.2.2.2.1 safe
    have h:=w.product pre0 f0
    rw [←eq,preOrder,fo] at h
    refine ⟨safe,h.1,?_⟩
    simp only [List.map_cons,List.sum_cons]
    omega

/-- One conjugate simultaneously bounds the complete sum of the losses. -/
theorem budget (w : ExtensionPlace p K) (hp : Prime p) (large : 5≤p) (away : p≠17)
    {r : K} (root : r^2=2) (a : Data) (valid : a.valid) {b : Rat} (live : b≠0)
    (pole : ThreeCoordinates.Sextic (17*b) (289-17*b)) (bt : b*a.trace^2=a.R)
    (odd : OddOrder (order p a.R)) :
    ∃ u : K, (u=r ∨ u= -r) ∧
      2*(a.steps.map (loss w u a.R a.delta)).sum ≤ order p a.R-1 := by
  obtain ⟨r0,d0,tn,td,chain,trace⟩:=valid
  have rt : (-r)^2=2 := by grobner
  obtain ⟨safe,x0,xv⟩:=chainOrderExact w hp r root r0 d0 odd chain
  obtain ⟨_,y0,yv⟩:=chainOrderExact w hp (-r) rt r0 d0 odd chain
  have rel:=evaluatedTrace w r root trace safe td
  rw [Q.eval_rational w r _ _ td] at rel
  have liveT : a.trace≠0 := fraction_nonzero tn td
  have im:=w.agrees a.trace liveT
  have prod:=w.product x0 y0
  have tot:=w.product im.1 prod.1
  change w.incl.map a.trace*(a.finalQ.eval w r*a.finalQ.eval w (-r))=_ at rel
  rw [rel,im.2,prod.2] at tot
  have lower := (toPlace w hp).add x0 y0 tot.1
  change min (w.val (a.finalQ.eval w r)) (w.val (a.finalQ.eval w (-r))) ≤
    w.val (a.finalQ.eval w r+a.finalQ.eval w (-r)) at lower
  rw [tot.2] at lower
  have vtrace : -max (w.val (a.finalQ.eval w r)) (w.val (a.finalQ.eval w (-r)))≤order p a.trace := by omega
  let v:=primeOrder p hp
  have ts:=power_order v liveT 2
  have vbrel:=v.mul _ _ live ts.1
  rw [bt,ts.2] at vbrel
  change order p a.R=order p b+2*order p a.trace at vbrel
  have oddB : OddOrder (order p b) := by
    obtain ⟨k,e⟩:=odd
    exact ⟨k-order p a.trace,by omega⟩
  have pos:=good_prime_positive hp large away live oddB pole
  by_cases h : w.val (a.finalQ.eval w (-r))≤w.val (a.finalQ.eval w r)
  · exact ⟨r,Or.inl rfl,by omega⟩
  · exact ⟨-r,Or.inr rfl,by omega⟩

theorem budget84 (x : Fin 84→Rat) (marked : Bool) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) (f : Frame) {p : Nat} (hp : Prime p) (large : 5≤p) (away : p≠17)
    {K : Type} [Field K] (w : ExtensionPlace p K) {r : K} (root : r^2=2)
    (odd : OddOrder (order p (f.data x).R)) :
    ∃ u : K, (u=r ∨ u= -r) ∧ 2*((f.data x).steps.map
      (loss w u (f.data x).R (f.data x).delta)).sum ≤ order p (f.data x).R-1 := by
  have dom:=fromZero_domain x marked active zero
  exact budget w hp large away root (f.data x) (actualDetector x dom f)
    (fraction_nonzero (safe_bN x dom f) (safe_bD x dom f))
    (physicalPole x marked active zero f) (literal_coefficient x dom f) odd

#print axioms budget84

private theorem lossNonneg (w : ExtensionPlace p K) (r : K) (R δ : Rat) (s : Step) :
    0≤loss w r R δ s := by
  classical
  unfold loss
  split <;> omega

private theorem sumBounds (w : ExtensionPlace p K) (r : K) (R δ : Rat) (ss : List Step) :
    0≤(ss.map (loss w r R δ)).sum ∧
    ∀ s∈ss, loss w r R δ s ≤ (ss.map (loss w r R δ)).sum := by
  induction ss with
  | nil => simp
  | cons a xs ih =>
    have ha:=lossNonneg w r R δ a
    simp only [List.map_cons,List.sum_cons]
    refine ⟨by omega,?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with eq|inTail
    · subst s;omega
    · have := ih.2 s inTail;omega

private theorem stepRaw (w : ExtensionPlace p K) (hp : Prime p) (large : 5≤p) (away : p≠17)
    {u : K} (root : u^2=2) {R δ : Rat} {s : Step} (proper : s.valid R δ)
    (rp : 0<order p R) (dp : 0≤order p δ)
    (cap : 2*loss w u R δ s≤order p R-1) (y0 : s.y.eval w u≠0) :
    (8*(s.m:Int)-7)*order p R+8*(s.m:Int)*order p δ+1≤8*w.val (s.y.eval w u) := by
  classical
  obtain ⟨mp,uy,uz,_,_,bnd,_,_⟩:=proper
  obtain ⟨cn,cv⟩:=cUnit w hp large away root
  obtain ⟨reg,formula⟩:=evaluatedBound w u root bnd uy uz
  have yy:=w.product y0 y0
  have cy:=w.product cn yy.1
  rw [cv,yy.2] at cy
  let z := s.z.eval w u
  let y := s.y.eval w u
  let c := C.eval w u
  have cleared : z*(1+c*(y*y))=c*(y*y) := by
    change s.z.eval w u*(1+scaled (C.eval w u) (s.y.eval w u))=_
    rw [formula];exact Field.div_mul_cancel reg
  have z0 : z≠0 := by
    intro hz
    rw [hz,Semiring.zero_mul] at cleared
    exact cy.1 cleared.symm
  have lower : (4*(s.m:Int)-3)*order p R+4*(s.m:Int)*order p δ-2*w.val z ≤ loss w u R δ s := by
    rw [loss,if_neg z0];exact Int.le_max_right _ _
  have scaledBound : (8*(s.m:Int)-7)*order p R+8*(s.m:Int)*order p δ+1≤4*w.val z := by
    have identity : (8*(s.m:Int)-7)*order p R+8*(s.m:Int)*order p δ+1 =
        2*((4*(s.m:Int)-3)*order p R+4*(s.m:Int)*order p δ)-order p R+1 := by grobner
    omega
  have nn := Int.mul_nonneg (show 0≤8*(s.m:Int)-8 by omega) (Int.le_of_lt rp)
  have dn := Int.mul_nonneg (show 0≤8*(s.m:Int) by omega) dp
  have id : (8*(s.m:Int)-7)*order p R=(8*(s.m:Int)-8)*order p R+order p R := by grobner
  have zp : 0<w.val z := by omega
  have one : (1:K)≠0:=Ne.symm Field.zero_ne_one
  have neg : -z≠0 := by intro zz;apply z0;grobner
  have unit := w.dominates (a:=(1:K)) (b:=-z) one
    (fun _=>by rw [oneOrder w hp,w.neg z z0];exact zp)
  rw [oneOrder w hp] at unit
  have relation : c*(y*y)*(1+ -z)=z := by grobner
  have vz := w.mul (c*(y*y)) (1+ -z) cy.1 unit.1
  rw [relation,unit.2] at vz
  have vc : w.val (c*(y*y))=0+(w.val y+w.val y) :=cy.2
  change _ ≤ 8*w.val y
  omega

/-- At each comparison row the order of contact and of the denominator contribute
to the depth of every nonzero raw test on one and the same conjugate. -/
theorem weightedRaw84 (x : Fin 84→Rat) (marked : Bool) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) (f : Frame) {p : Nat} (hp : Prime p) (large : 5≤p) (away : p≠17)
    {K : Type} [Field K] (w : ExtensionPlace p K) {r : K} (root : r^2=2)
    (odd : OddOrder (order p (f.data x).R)) (dp : 0≤order p (f.data x).delta) :
    ∃ u : K, (u=r ∨ u= -r) ∧ ∀ s∈(f.data x).steps, s.y.eval w u≠0 →
        (8*(s.m:Int)-7)*order p (f.data x).R+8*(s.m:Int)*order p (f.data x).delta+1
          ≤8*w.val (s.y.eval w u) := by
  obtain ⟨u,sign,b⟩ := budget84 x marked active zero f hp large away w root odd
  have ur : u^2=2 := by rcases sign with e|e <;> rw [e] <;> grobner
  have sums:=sumBounds w u (f.data x).R (f.data x).delta (f.data x).steps
  have dom:=fromZero_domain x marked active zero
  obtain ⟨r0,d0,_,_,chain,_⟩:=actualDetector x dom f
  obtain ⟨_,_,_,valid⟩:=chainOrder w hp ur r0 d0 dp odd chain
  refine ⟨u,sign,?_⟩
  intro s hs
  have seen:=sums.2 s hs
  exact stepRaw w hp large away ur (valid s hs).1 (by omega) dp (by omega)

#print axioms weightedRaw84
end ComparisonBudget
