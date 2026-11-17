import ChordDepth

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic
attribute [local instance] Semiring.natCast Ring.intCast

variable {K G : Type} [Field K] [IntModule G]

/-- Ordinary projective group geometry. In the open set Y≠0 we normalize
to (t:-1:s). Reflection and three intersections on a line are the geometric
group law. No valuation, local domain, or scalar occurs in these data. -/
structure ProjectiveGroup (D : K) (G : Type) [IntModule G] where
  t : G → K
  s : G → K
  defined : G → Prop
  origin : defined 0 ∧ t 0=0 ∧ s 0=0
  equation : ∀ Q, defined Q → OnCurve D (t Q) (s Q)
  atInfinity : ∀ Q, defined Q → t Q=0 → s Q=0 → Q=0
  reflect : ∀ Q, defined Q → defined (-Q) ∧ t (-Q)= -(t Q) ∧ s (-Q)= -(s Q)
  sum : ∀ P Q l k h, defined P → defined Q →
    s P=l*t P+k → s Q=l*t Q+k → Intersections D l k (t P) (t Q) h →
    defined (P+Q) ∧ t (P+Q)=h ∧ s (P+Q)=l*h-k

variable {p : Nat} {D : K} (M : ProjectiveGroup D G) (w : ExtensionPlace p K)

/-- Formality means that the normalized projective point reduces to infinity. -/
def ProjectiveGroup.formal (Q : G) := M.defined Q ∧ w.deep 1 (M.t Q) ∧ w.deep 1 (M.s Q)

theorem ProjectiveGroup.zero_parameter {Q : G} (dom : M.defined Q) (zero : M.t Q=0) : Q=0 := by
  have eq:=M.equation Q dom
  unfold OnCurve at eq
  rw [zero] at eq
  exact M.atInfinity Q dom zero (by grobner)

private theorem sum_step {P Q : G} {d : Int} (hd : 0<d) (hD : w.deep 0 D)
    (Pd : M.defined P) (Qd : M.defined Q)
    (hP : Layer w d (M.t P) (M.s P)) (hQ : Layer w d (M.t Q) (M.s Q)) :
    M.defined (P+Q) ∧ Layer w d (M.t (P+Q)) (M.s (P+Q)) ∧
    w.deep (5*d) (M.t (P+Q)-M.t P-M.t Q) := by
  let c:=chord w hd hD (M.equation P Pd) (M.equation Q Qd) hP hQ
  obtain ⟨op,t,s⟩:=M.sum P Q _ _ _ Pd Qd c.atLeft c.atRight c.intersection
  rw [t,s]
  exact ⟨op,c.layer,c.error⟩

/-- Every signed multiple has additive parameter modulo depth 5d, simultaneously
including zero and exact cancellation. There is no hypothesis on an integer multiplier. -/
theorem ProjectiveGroup.signed {Q : G} {d : Int} (hD : w.deep 0 D)
    (pos : 0<d) (dom : M.defined Q) (seed : Layer w d (M.t Q) (M.s Q)) (n : Int) :
    M.defined (n • Q) ∧ Layer w d (M.t (n • Q)) (M.s (n • Q)) ∧
    w.deep (5*d) (M.t (n • Q)-(n:K)*M.t Q) := by
  have posCase (j : Nat) : M.defined ((j:Int) • Q) ∧
      Layer w d (M.t ((j:Int) • Q)) (M.s ((j:Int) • Q)) ∧
      w.deep (5*d) (M.t ((j:Int) • Q)-((j:Int):K)*M.t Q) := by
    induction j with
    | zero =>
      simp only [Int.natCast_zero,IntModule.zero_zsmul,M.origin.2.1,M.origin.2.2,
        Ring.intCast_zero,Semiring.zero_mul,show (0:K)-0=0 by grobner]
      exact ⟨M.origin.1,⟨deep_zero w _,deep_zero w _⟩,deep_zero w _⟩
    | succ j ih =>
      obtain ⟨op,live,err⟩:=ih
      obtain ⟨out,layer,correction⟩:=sum_step M w pos hD op dom live seed
      rw [Int.natCast_succ,IntModule.add_zsmul,IntModule.one_zsmul,Ring.intCast_add,Ring.intCast_one]
      refine ⟨out,layer,?_⟩
      rw [show M.t ((j:Int) • Q+Q)-(((j:Int):K)+1)*M.t Q =
          (M.t ((j:Int) • Q+Q)-M.t ((j:Int) • Q)-M.t Q)+(M.t ((j:Int) • Q)-((j:Int):K)*M.t Q) by grobner]
      exact w.deep_add correction err
  cases n with
  | ofNat j => exact posCase j
  | negSucc j =>
    obtain ⟨op,live,err⟩:=posCase (j+1)
    obtain ⟨neg,nt,ns⟩:=M.reflect _ op
    rw [show Int.negSucc j= -((j+1:Nat):Int) by omega,IntModule.neg_zsmul,nt,ns,Ring.intCast_neg]
    refine ⟨neg,⟨deep_neg w live.1,deep_neg w live.2⟩,?_⟩
    rw [show -M.t (((j+1:Nat):Int) • Q)-(-(((j+1:Nat):Int):K))*M.t Q =
        -(M.t (((j+1:Nat):Int) • Q)-(((j+1:Nat):Int):K)*M.t Q) by grobner]
    exact deep_neg w err

private theorem formal_of_layer {Q : G} {d : Int} (dom : M.defined Q) (hd : 0<d)
    (lay : Layer w d (M.t Q) (M.s Q)) : M.formal w Q :=
  ⟨dom,deep_lower w (by omega) lay.1,deep_lower w (by omega) lay.2⟩

/-- Construction of the scalar chart's tangent law from
ordinary projective group geometry and the integral coefficient D. -/
def ProjectiveGroup.multiplicationChart (hD : w.deep 0 D) : MultiplicationChart p w G where
  formal:=M.formal w
  z:=M.t
  origin:=M.origin.2.1
  tangent:=by
    intro n Q _ domain nz hd
    have lay:=layer_of_reduction w (d:=w.val (M.t Q)) (by omega) hD (M.equation Q domain.1)
      (fun _=>Int.le_refl _) domain.2.2
    obtain ⟨op,layer,est⟩:=M.signed w hD (by omega) domain.1 lay n
    let r:=M.t (n • Q)-(n:K)*M.t Q
    let t:=M.t Q
    have t2:=w.product nz nz
    let e:=r/(t*t)
    have clear : e*(t*t)=r := Field.div_mul_cancel t2.1
    refine ⟨formal_of_layer M w op (by omega) layer,e,?_,?_⟩
    · intro en
      obtain ⟨er,ve⟩:=w.product en t2.1
      change e*(t*t)≠0 at er
      change w.val (e*(t*t))=w.val e+w.val (t*t) at ve
      rw [clear] at er ve
      have := est er
      change 5*w.val t≤w.val r at this
      have vt : w.val (t*t)=w.val t+w.val t := t2.2
      change 2≤w.val t at hd
      omega
    · change M.t (n • Q)=t*((n:K)+t*e)
      calc M.t (n • Q)=(n:K)*t+r := by dsimp [r,t];grobner
           _=t*((n:K)+t*e) := by rw [←clear];grobner

private theorem step_order {Q : G} {a : Int} (hD : w.deep 0 D)
    (dom : M.formal w Q) (nz : M.t Q≠0) (an : a≠0) (small : order p (a:Rat)≤1) :
    M.formal w (a • Q) ∧ M.t (a • Q)≠0 ∧ w.val (M.t (a • Q))=w.val (M.t Q)+order p (a:Rat) := by
  let d:=w.val (M.t Q)
  have pos : 0<d := dom.2.1 nz
  have lay:=layer_of_reduction w (d:=d) pos hD (M.equation Q dom.1) (fun _=>Int.le_refl _) dom.2.2
  obtain ⟨op,layer,err⟩:=M.signed w hD pos dom.1 lay a
  obtain ⟨ne,ord⟩:=w.on_int an
  have ⟨product,prodOrder⟩:=w.product ne nz
  have low : M.t (a • Q)-(a:K)*M.t Q≠0 →
      w.val ((a:K)*M.t Q)<w.val (M.t (a • Q)-(a:K)*M.t Q) := by
    intro live
    have := err live
    rw [prodOrder,ord]
    change order p (a:Rat)+d<_
    omega
  have h:=w.dominates product low
  rw [show (a:K)*M.t Q+(M.t (a • Q)-(a:K)*M.t Q)=M.t (a • Q) by grobner,prodOrder,ord,Int.add_comm] at h
  exact ⟨formal_of_layer M w op pos layer,h⟩

/-- Exact signed growth already at depth one. The quartic gap after the
linear term also suffices for p=2. -/
theorem ProjectiveGroup.exact_order (hp : Prime p) (hD : w.deep 0 D)
    {Q : G} (dom : M.formal w Q) (nz : M.t Q≠0) {a : Int} (an : a≠0) :
    M.formal w (a • Q) ∧ M.t (a • Q)≠0 ∧
    w.val (M.t (a • Q))=w.val (M.t Q)+order p (a:Rat) := by
  obtain ⟨u,fact,unit⟩:=int_split hp.1 a an
  have un : u≠0 := fun e=>unit (e ▸ Int.dvd_zero _)
  have ou:=order_int_unit hp unit
  have first:=step_order M w hD dom nz un (by omega)
  have pz : (p:Int)≠0 := by have :=hp.1;omega
  have op : order p ((p:Int):Rat)=1 := by rw [Rat.intCast_natCast];exact order_prime hp
  have power (k : Nat) : M.formal w (((p:Int)^k) • (u • Q)) ∧
      M.t (((p:Int)^k) • (u • Q))≠0 ∧ w.val (M.t (((p:Int)^k) • (u • Q)))=w.val (M.t Q)+(k:Int) := by
    induction k with
    | zero => simpa only [Int.pow_zero,IntModule.one_zsmul,ou,Int.add_zero,Int.natCast_zero] using first
    | succ k ih =>
      obtain ⟨formal,live,v⟩:=ih
      have h:=step_order M w hD formal live pz (by omega)
      rw [v,op] at h
      rw [Int.pow_succ,Int.mul_comm ((p:Int)^k),IntModule.mul_zsmul,Int.natCast_succ,←Int.add_assoc]
      exact h
  have h:=power (intOrder p a)
  rw [←IntModule.mul_zsmul,←fact] at h
  rwa [order_int hp]

end ProjectionFibres
