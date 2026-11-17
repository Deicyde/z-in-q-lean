import AnchorShift

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic ProgressionWitnesses.SingleContact
attribute [local instance] Semiring.natCast Ring.intCast

variable {K G : Type} [Field K] [IntModule G] {p : Nat} {rho : K}
variable {w : ExtensionPlace p K} {M : ProjectiveGroup ((3-rho)^2) G}

/-- Only H's reciprocal, R's parameter, and their physical ratio are read.
There is no doubled-point coordinate or affine tangent in this input. -/
structure ScalarSource (w : ExtensionPlace p K) {rho : K} (M : ProjectiveGroup ((3-rho)^2) G)
    (m n : Int) (u v : Rat) where
  root : rho^2=2
  P₀ : G
  torsion : G
  twice : (2:Int) • torsion=0
  shared : AffineAt M (m • P₀+torsion)
  defined : M.defined ((n-1) • ((2:Int) • P₀))
  ratio : M.t ((n-1) • ((2:Int) • P₀))=
    M.t (m • P₀+torsion)*(w.incl.map u+w.incl.map v*rho)

private theorem lift_depth {a : Rat} (h : a≠0 → 17≤order p a) : w.deep 17 (w.incl.map a) := by
  intro ne
  have az : a≠0 := fun z=>ne (by rw [z,w.incl.zero])
  rw [(w.agrees a az).2];exact h az

theorem ScalarSource.divides {m n : Int} {u v : Rat}
    (b : ScalarSource w M m n u v) (A : ZeroAnchor M) (hp : Prime p) (large : 5≤p)
    (high : 8<w.val b.shared.f) (hu : u≠0 → 17≤order p u) (hv : v≠0 → 17≤order p v) :
    ((p^17:Nat):Int)∣n-1 := by
  let H:=m • b.P₀+b.torsion
  let R:=(n-1) • ((2:Int) • b.P₀)
  obtain ⟨rn,vr,hD⟩:=curve_coeffs w hp large b.root
  have fz:=formal_parameter w hp hD b.shared.toAffineValue (by omega)
  change w.val b.shared.f=2*w.val (M.t H) at fz
  have dh : 2≤w.val (M.t H) := by omega
  have formalH : M.formal w H := b.shared.formal_of_reciprocal hp hD (by omega)
  by_cases zr : M.t R=0
  · have origin : R=0 := M.zero_parameter b.defined zr
    have identity:=scalar_group_identity m n b.P₀ b.torsion b.twice
    change m • ((2:Int) • R)=(4*(n-1)) • H at identity
    rw [origin,IntModule.zsmul_zero,IntModule.zsmul_zero] at identity
    by_cases sn : n-1=0
    · rw [sn];exact Int.dvd_zero _
    have nonzero : 4*(n-1)≠0 := by omega
    have outside : M.t ((4*(n-1)) • H)≠0 := (M.exact_order w hp hD formalH b.shared.live.2.2 nonzero).2.1
    rw [←identity,M.origin.2.1] at outside
    exact False.elim (outside rfl)
  have rr : w.deep 0 rho := fun _=>by omega
  have vd:=deep_mul w (lift_depth (w:=w) hv) rr
  have both:=w.deep_add (lift_depth (w:=w) hu) (deep_lower w (by omega) vd)
  have ratio : M.t R=M.t H*(w.incl.map u+w.incl.map v*rho) := b.ratio
  have sn : w.incl.map u+w.incl.map v*rho≠0 := fun z=>zr (by rw [ratio,z,Semiring.mul_zero])
  have bound:=both sn
  have vv:=w.mul (M.t H) _ b.shared.live.2.2 sn
  rw [←ratio] at vv
  have positive : 0<w.val (M.t R) := by omega
  have disc:=actual_discriminant w b.root
  have dn : (3-rho)^2≠0 := by intro z;apply disc;rw [z];grobner
  obtain ⟨B,dom,tn,same,twice⟩:=A.formal_representative w dn b.defined zr positive
  have dup:=M.exact_order w hp hD dom tn (a:=2) (by decide)
  have ou : order p (2:Rat)=0 := order_nat_unit (n:=2) hp (fun dvd =>by have :=Nat.le_of_dvd (by decide : 0<2) dvd;omega)
  change M.formal w ((2:Int) • B) ∧ M.t ((2:Int) • B)≠0 ∧ w.val (M.t ((2:Int) • B))=w.val (M.t B)+order p (2:Rat) at dup
  rw [twice,ou,Int.add_zero,same] at dup
  apply index_divisor (M.multiplicationChart w hD) hp large (scalar_group_identity m n b.P₀ b.torsion b.twice)
    formalH b.shared.live.2.2 dh dup.1 dup.2.1
  change w.val (M.t H)+17≤w.val (M.t ((2:Int) • R))
  have v2 : w.val (M.t ((2:Int) • R))=w.val (M.t R) := dup.2.2
  omega

/-- At one physical scalar contact the divisibility follows from source-point
coordinates at H,R on both conjugates and ordinary projective chord geometry. -/
theorem source_scalar_divisor {G' : Type} [IntModule G']
    (M : ProjectiveGroup ((3-rho)^2) G) (N : ProjectiveGroup ((3-(-rho))^2) G')
    (A : ZeroAnchor M) (B : ZeroAnchor N)
    {m n : Int} {r u v q U W b : Rat} (hp : Prime p) (large : 5≤p) (away : p≠17)
    (contact : 0<order p r) (odd : OddOrder (order p r)) (hr : r≠0)
    (values : ScalarValues r u v q U W b) (point : ThreeCoordinates.Sextic (17*b) (289-17*b))
    (left : ScalarSource w M m n u v) (right : ScalarSource w N m n u v)
    (norm : w.incl.map q=left.shared.f*right.shared.f) : ((p^17:Nat):Int)∣n-1 := by
  obtain ⟨_,_,_,dq,du,dv⟩:=scalar_depths hp large away hr odd values point
  have highU (nz : u≠0) : 17≤order p u := by have h:=du nz;omega
  have highV (nz : v≠0) : 17≤order p v := by have h:=dv nz;omega
  obtain ⟨product,orders⟩:=w.product left.shared.live.1 right.shared.live.1
  have nq : q≠0 := fun z=>product (by rw [←norm,z,w.incl.zero])
  have qv:=dq nq
  have eq:=(w.agrees q nq).2
  rw [norm,orders] at eq
  by_cases h : 8<w.val left.shared.f
  · exact left.divides A hp large h highU highV
  · exact right.divides B hp large (by omega) highU highV

end ProjectionFibres
