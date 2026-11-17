import ProjectiveScalar

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic
attribute [local instance] Semiring.natCast Ring.intCast

variable {K G : Type} [Field K] [IntModule G] {D : K}

/-- The line X=tU through (0:0:1), parametrized by (tU:-U:V), meets
the anchor at U=0 and has residual intersections s and v. -/
def AnchorIntersections (D t s v : K) : Prop := D*t≠0 ∧ ∀ U V : K,
    U^2*V-t^3*U^3+D*t*U*V^2=D*t*U*(V-s*U)*(V-v*U)

theorem anchor_factor {t s : K} (eq : OnCurve D t s) (nz : D*t≠0) :
    AnchorIntersections D t s (-s-1/(D*t)) := by
  have unit : (1/(D*t))*(D*t)=1 := Field.div_mul_cancel nz
  let v := -s-1/(D*t)
  have sum : D*t*(s+v)= -1 := by dsimp [v];grobner
  have prod : D*t*s*v= -t^3 := by
    have x:=congrArg (·*s) unit
    unfold OnCurve at eq
    dsimp [v];grobner
  refine ⟨nz,fun U V=>?_⟩
  change _=D*t*U*(V-s*U)*(V-v*U)
  calc _= D*t*U*V^2- (D*t*(s+v))*U^2*V+(D*t*s*v)*U^3 := by rw [sum,prod];grobner
       _=_ := by grobner

/-- The additional family of ordinary projective lines through the literal
two-torsion point (0:0:1). The anchor lies outside the patch Y≠0. -/
structure ZeroAnchor (M : ProjectiveGroup D G) where
  T : G
  twice : (2:Int) • T=0
  line : ∀ Q v, M.defined Q → AnchorIntersections D (M.t Q) (M.s Q) v →
    M.defined (Q+T) ∧ M.t (Q+T)= -M.t Q ∧ M.s (Q+T)= -v

variable {p : Nat} (w : ExtensionPlace p K)

private theorem one_order : (1:K)≠0 ∧ w.val 1=0 := by
  have nz : (1:K)≠0 := fun e=>Field.zero_ne_one e.symm
  have h:=w.mul 1 1 nz nz;rw [Semiring.one_mul] at h
  exact ⟨nz,by omega⟩

/-- When t has positive order, one of the two residual intersections has
second-coordinate order at least one. If the given s is outside, the reflected
other intersection has order exactly 3v(t), even when D is a nonunit. -/
theorem other_intersection_depth {t s : K} (dn : D≠0) (eq : OnCurve D t s)
    (tn : t≠0) (positive : 0<w.val t) (sn : s≠0) (outside : w.val s≤0) :
    let v:= -s-1/(D*t)
    (-v)≠0 ∧ w.val (-v)=3*w.val t := by
  let L:=D*t
  let A:=1+L*s
  have l := w.product dn tn
  have ls := w.product l.1 sn
  have tt:=w.product tn tn
  have cube:=w.product tt.1 tn
  have fac : s*A=t*t*t := by dsimp [A,L];unfold OnCurve at eq;grobner
  have an : A≠0 := fun z=>cube.1 (by rw [←fac,z,Semiring.mul_zero])
  have sa:=w.mul s A sn an
  rw [fac,cube.2,tt.2] at sa
  have high : 0<w.val A := by omega
  obtain ⟨one,vo⟩:=one_order w
  have zero : w.val (L*s)=0 := by
    apply Classical.byContradiction
    intro ne
    have h:=w.addUnequal 1 (L*s) one ls.1 (by omega)
    have vsum : w.val A=min (w.val 1) (w.val (L*s)) := h.2
    omega
  let v:= -s-1/L
  have clear : (-v)*L=A := by
    have inverse : (1/L)*L=1 := Field.div_mul_cancel l.1
    dsimp [v,A];grobner
  have vn : -v≠0 := fun z=>an (by rw [←clear,z,Semiring.zero_mul])
  have vv:=w.mul (-v) L vn l.1;rw [clear] at vv
  have vprod : w.val (L*s)=w.val L+w.val s := ls.2
  change (-v)≠0 ∧ w.val (-v)=3*w.val t
  exact ⟨vn,by omega⟩

/-- Choose Q or its translate by (0,0). They have equal doubled point,
equal parameter depth and one belongs to the formal neighborhood. -/
theorem ZeroAnchor.formal_representative {M : ProjectiveGroup D G} (A : ZeroAnchor M)
    (dn : D≠0) {Q : G} (defined : M.defined Q) (tn : M.t Q≠0) (positive : 0<w.val (M.t Q)) :
    ∃ B, M.formal w B ∧ M.t B≠0 ∧ w.val (M.t B)=w.val (M.t Q) ∧ (2:Int) • B=(2:Int) • Q := by
  by_cases inside : w.deep 1 (M.s Q)
  · exact ⟨Q,⟨defined,fun _=>positive,inside⟩,tn,rfl,rfl⟩
  have sn : M.s Q≠0 := fun e=>inside (by rw [e];exact deep_zero w _)
  have outside : w.val (M.s Q)≤0 := by
    apply Int.le_of_not_gt;intro h;exact inside (fun _=>h)
  have eq:=M.equation Q defined
  obtain ⟨live,depth⟩:=other_intersection_depth w dn eq tn positive sn outside
  obtain ⟨dom,t,s⟩:=A.line Q _ defined (anchor_factor eq (w.product dn tn).1)
  have nt : -M.t Q≠0 := by intro h;apply tn;grobner
  refine ⟨Q+A.T,?_,t ▸ nt,?_,?_⟩
  · refine ⟨dom,?_,?_⟩
    · rw [t];exact fun _=>by rw [w.neg _ tn];omega
    · rw [s];exact fun _=>by rw [depth];omega
  · rw [t,w.neg _ tn]
  · rw [IntModule.zsmul_add,A.twice,AddCommMonoid.add_zero]

end ProjectionFibres
