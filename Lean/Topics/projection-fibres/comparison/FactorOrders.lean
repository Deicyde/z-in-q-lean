import DetectorData
namespace ProjectionFibres.Comparison
open StructuralReduction ProgressionWitnesses.SingleContact BinaryQuartic Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

variable {p : Nat} {K : Type} [Field K] (w : ExtensionPlace p K)

private theorem one_value (hp : Prime p) : w.val 1=0 := by
  have e:=(w.agrees 1 (by decide)).2
  rw [w.incl.one] at e
  exact e.trans (primeOrder p hp).one

def toPlace (hp : Prime p) : Place K where
  v:=w.val
  one:=one_value w hp
  mul:=fun hx hy=>w.mul _ _ hx hy
  add:=fun {a b} _ _ sum=>w.deep_add (d:=min (w.val a) (w.val b))
        (fun _=>Int.min_le_left _ _) (fun _=>Int.min_le_right _ _) sum
  unequal:=fun x y=>w.addUnequal _ _ x y

theorem weightOrder (hp : Prime p) {r delta : Rat} (r0 : r≠0) (d0 : delta≠0)
    {s : Step} (h : s.valid r delta) :
    s.weight≠0 ∧ order p s.weight=(3-4*(s.m:Int))*order p r-4*(s.m:Int)*order p delta := by
  have eq:=h.2.2.2.2.2.2.2
  have qz : s.weight≠0 := by intro z;rw [z,Rat.zero_mul,Rat.zero_mul] at eq;contradiction
  let v:=primeOrder p hp
  obtain ⟨rp,rv⟩:=power_order v r0 (4*s.m-3)
  obtain ⟨dp,dv⟩:=power_order v d0 (4*s.m)
  have pr : s.weight*r^(4*s.m-3)≠0 := fun z=>(Rat.mul_eq_zero.mp z).elim qz rp
  have e:=congrArg v.ord eq
  rw [v.mul _ _ pr dp,v.mul _ _ qz rp,rv,dv,v.one] at e
  change order p s.weight+((4*s.m-3:Nat):Int)*order p r+((4*s.m:Nat):Int)*order p delta=0 at e
  have exponent : ((4*s.m-3:Nat):Int)=4*(s.m:Int)-3 := by have :=h.1;omega
  rw [exponent,Int.natCast_mul] at e
  refine ⟨qz,?_⟩
  change order p s.weight+(4*(s.m:Int)-3)*order p r+4*(s.m:Int)*order p delta=0 at e
  grobner

theorem cUnit (hp : Prime p) (large : 5≤p) (away : p≠17) {r : K} (root : r^2=2) :
    C.eval w r≠0 ∧ w.val (C.eval w r)=0 := by
  have p2 : ¬p∣2 := fun h=>by have :=Nat.le_of_dvd (by decide : 0<2) h;omega
  have two:=w.on_int (n:=2) (by decide)
  have o2 : order p ((2:Int):Rat)=0:=order_nat_unit (n:=2) hp p2
  rw [o2] at two
  have two' : ((2:Int):K)=(2:K) := by grobner
  rw [two'] at two
  have rne : r≠0 := by intro z;rw [z,show (0:K)^2=0 by grobner] at root;exact two.1 root.symm
  have pp:=w.mul r r rne rne
  rw [show r*r=r^2 by grobner,root,two.2] at pp
  have ro : w.val r=0 := by omega
  have neg : -r≠0 := by intro z;apply rne;grobner
  have plus : w.deep 0 (2+r) := w.deep_add (fun _=>Int.le_of_eq two.2.symm) (fun _=>Int.le_of_eq ro.symm)
  have minus : w.deep 0 (2+(-r)) := w.deep_add (fun _=>Int.le_of_eq two.2.symm)
    (fun _=>Int.le_of_eq ((w.neg r rne).trans ro).symm)
  have ident : ((2:K)+r)*(2+(-r))=2 := by grobner
  have live : ((2:K)+r)≠0 := by intro z;rw [z,Semiring.zero_mul] at ident;exact two.1 ident.symm
  have live' : ((2:K)+(-r))≠0 := by intro z;rw [z,Semiring.mul_zero] at ident;exact two.1 ident.symm
  have sum:=w.mul _ _ live live'
  rw [ident,two.2] at sum
  have plus0 : w.val (2+r)=0 := by have :=plus live;have :=minus live';omega
  have fifty := w.on_int (n:=51) (by decide)
  have eq51 : order p ((51:Int):Rat)=0 := by
    have ez : ((51:Int):Rat)=3*17 := by grobner
    have prod:=(primeOrder p hp).mul (3:Rat) (17:Rat) (by decide) (by decide)
    change order p (3*17)=order p 3+order p 17 at prod
    rw [ez,prod,three_unit hp large,seventeen_unit hp away]
    decide
  have fifty' : ((51:Int):K)=(51:K) := by grobner
  rw [fifty'] at fifty
  have c : C.eval w r=(51:K)*(2+r) := by
    rw [C,Q.eval_constant]
    have a : w.incl.map 102=(102:K) := by
      calc _=w.incl.map ((102:Int):Rat) := congrArg _ (by decide)
           _=((102:Int):K) := w.incl.int 102
           _=102 := by grobner
    have b : w.incl.map 51=(51:K) := by
      calc _=w.incl.map ((51:Int):Rat) := congrArg _ (by decide)
           _=((51:Int):K) := w.incl.int 51
           _=51 := by grobner
    rw [a,b];grobner
  have val:=w.product fifty.1 live
  rw [←c,fifty.2,eq51,plus0,Int.add_zero] at val
  exact val

private theorem stepFactor (hp : Prime p) {rho : K} (root : rho^2=2) {R delta : Rat}
    (R0 : R≠0) (d0 : delta≠0) (dd : 0≤order p delta) (odd : OddOrder (order p R))
    {s : Step} (valid : s.valid R delta) :
    s.factor.eval w rho≠0 ∧ w.val (s.factor.eval w rho)≤0 ∧
    (s.z.eval w rho≠0 → w.val (s.factor.eval w rho)≤
      (1-2*(2*(s.m:Int)-1))*order p R+2*w.val (s.z.eval w rho)) := by
  have keep:=valid
  obtain ⟨mpos,_,uz,uq,uf,_,plus,_⟩:=keep
  have f:=evaluatedFactor w rho root plus uz uq uf
  rw [Q.eval_rational w rho _ _ uq] at f
  have one : (1:K)≠0 :=Ne.symm Field.zero_ne_one
  have vo:=one_value w hp
  obtain ⟨qn,qv⟩:=weightOrder hp R0 d0 valid
  have incl:=w.agrees s.weight qn
  change _=1+w.incl.map s.weight*(s.z.eval w rho*s.z.eval w rho) at f
  by_cases zero : s.z.eval w rho=0
  · rw [zero,Semiring.zero_mul,Semiring.mul_zero,AddCommMonoid.add_zero] at f
    exact ⟨f ▸ one,by rw [f,vo];omega,fun ne=>False.elim (ne zero)⟩
  have zz:=w.product zero zero
  have term:=w.product incl.1 zz.1
  rw [zz.2,incl.2,qv] at term
  have e : OddOrder (w.val (w.incl.map s.weight*(s.z.eval w rho*s.z.eval w rho))) := by
    obtain ⟨k,ek⟩:=odd
    refine ⟨3*k+1-2*(s.m:Int)*order p R-2*(s.m:Int)*order p delta+w.val (s.z.eval w rho),?_⟩
    rw [term.2,ek];grobner
  have ne : w.val (1:K)≠ w.val (w.incl.map s.weight*(s.z.eval w rho*s.z.eval w rho)) := by
    obtain ⟨k,h⟩:=e;omega
  obtain ⟨f0,fo⟩:=w.addUnequal _ _ one term.1 ne
  rw [←f] at fo f0
  rw [vo,term.2] at fo
  have bound:=Int.min_le_right 0 ((3-4*(s.m:Int))*order p R-4*(s.m:Int)*order p delta+
      (w.val (s.z.eval w rho)+w.val (s.z.eval w rho)))
  rw [←fo] at bound
  have nonnegative:=Int.mul_nonneg (show 0≤4*(s.m:Int) by omega) dd
  have hcoef : 1-2*(2*(s.m:Int)-1)=3-4*(s.m:Int) := by grobner
  exact ⟨f0,by rw [fo];exact Int.min_le_left _ _,fun _=>by rw [hcoef];omega⟩

theorem chainOrder (hp : Prime p) {rho : K} (root : rho^2=2) {R delta : Rat}
    (R0 : R≠0) (d0 : delta≠0) (dd : 0≤order p delta) (odd : OddOrder (order p R))
    {xs W} (chain : Chain R delta xs W) :
    W.d≠0 ∧ W.eval w rho≠0 ∧ w.val (W.eval w rho)≤0 ∧
    ∀ s∈xs, s.valid R delta ∧ (s.z.eval w rho≠0 → w.val (W.eval w rho)≤
       (1-2*(2*(s.m:Int)-1))*order p R+2*w.val (s.z.eval w rho)) := by
  induction chain with
  | nil => exact ⟨by decide,(eval_one w rho) ▸ Ne.symm Field.zero_ne_one,by rw [eval_one,one_value w hp];omega,fun _ h=>by contradiction⟩
  | add old s after valid safe eq ih =>
    obtain ⟨ub,b0,bo,all⟩:=ih
    obtain ⟨f0,fo,fb⟩:=stepFactor w hp root R0 d0 dd odd valid
    have v:=(evaluatedProduct w rho root eq ub valid.2.2.2.2.1 safe)
    have step:=w.product b0 f0
    rw [←v] at step
    refine ⟨safe,step.1,by omega,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with head|tail
    · subst t;exact ⟨valid,fun nn=>by have :=fb nn;omega⟩
    · obtain ⟨vt,b⟩:=all t tail;exact ⟨vt,fun nn=>by have :=b nn;omega⟩

end ProjectionFibres.Comparison
