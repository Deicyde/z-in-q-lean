import ChordMultiplication

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic ProgressionWitnesses.SingleContact
attribute [local instance] Semiring.natCast Ring.intCast

variable {K G : Type} [Field K] [IntModule G] {p : Nat} {D : K}
variable {w : ExtensionPlace p K} {M : ProjectiveGroup D G}

/-- The source affine point has ordinary coordinates (x:y:1)=(t:-1:s).
The equality for s records the ordinate on the actual point, which matters
because two different affine branches can have the same t. -/
structure AffineAt (M : ProjectiveGroup D G) (Q : G) extends AffineValue D (M.t Q) where
  defined : M.defined Q
  ordinate : M.s Q*y= -1

theorem AffineAt.second {Q : G} (a : AffineAt M Q) : M.s Q = M.t Q*a.f := by
  have coord:=(affine_to_chart a.toAffineValue).2
  have yn : a.y≠0 := by
    intro eq
    have e:=a.ordinate
    rw [eq,Semiring.mul_zero] at e
    apply Field.zero_ne_one (α:=K)
    grobner
  apply cancel_unit ⟨_,Field.inv_mul_cancel yn⟩
  calc a.y*M.s Q= -1 := by rw [CommSemiring.mul_comm,a.ordinate]
       _=a.y*(M.t Q*a.f) := by rw [CommSemiring.mul_comm];exact coord.symm

theorem AffineAt.formal_of_reciprocal {Q : G} (a : AffineAt M Q) (hp : Prime p) (hD : w.deep 0 D)
    (positive : 0<w.val a.f) : M.formal w Q := by
  have ⟨pos,lay⟩:=affine_layer w hp hD a.toAffineValue positive
  change 0<w.val (M.t Q) at pos
  refine ⟨a.defined,deep_lower w (by omega) lay.1,?_⟩
  rw [a.second]
  exact deep_lower w (by omega) lay.2

/-- For rho²=2 the short curve discriminant 64D³ is nonzero in characteristic zero. -/
theorem actual_discriminant (w : ExtensionPlace p K) {rho : K} (root : rho^2=2) :
    64*((3-rho)^2)^3≠0 := by
  have nz7 : (7:K)≠0 := by
    have h:=(w.on_int (n:=((7:Nat):Int)) (by decide)).1
    rwa [Ring.intCast_natCast,←Semiring.ofNat_eq_natCast 7] at h
  have nz64 : (64:K)≠0 := by
    have h:=(w.on_int (n:=((64:Nat):Int)) (by decide)).1
    rwa [Ring.intCast_natCast,←Semiring.ofNat_eq_natCast 64] at h
  have n : 3-rho≠0 := by
    intro eq
    apply nz7
    have r : rho=3 := by grobner
    rw [r] at root
    grobner
  have sq : (3-rho)^2≠0 := by
    rw [show (3-rho)^2=(3-rho)*(3-rho) by grobner]
    exact (w.product n n).1
  have cb : ((3-rho)^2)^3≠0 := by
    rw [show ((3-rho)^2)^3=(3-rho)^2*(3-rho)^2*(3-rho)^2 by grobner]
    exact (w.product (w.product sq sq).1 sq).1
  exact (w.product nz64 cb).1

/-- Raw affine source data of one conjugate. The local domain tests and all
multiplication estimates are consequences of projective geometry. -/
structure ProjectiveBranch (w : ExtensionPlace p K) {rho : K} (M : ProjectiveGroup ((3-rho)^2) G)
    (m n : Int) (u v : Rat) where
  root : rho^2=2
  P₀ : G
  torsion : G
  twoTorsion : (2:Int) • torsion=0
  shared : AffineAt M (m • P₀+torsion)
  original : AffineAt M ((n-1) • ((2:Int) • P₀))
  doubled : AffineAt M ((2:Int) • ((n-1) • ((2:Int) • P₀)))
  slope : K
  tangent : 2*original.y*slope=3*original.x^2-(3-rho)^2
  abscissa : doubled.x=slope^2-2*original.x
  ratio : M.t ((n-1) • ((2:Int) • P₀))=
    M.t (m • P₀+torsion)*(w.incl.map u+w.incl.map v*rho)

def ProjectiveBranch.toScalar {rho : K} {M : ProjectiveGroup ((3-rho)^2) G}
    {m n : Int} {u v : Rat} (b : ProjectiveBranch w M m n u v)
    (hp : Prime p) (hD : w.deep 0 ((3-rho)^2)) :
    ScalarBranch (M.multiplicationChart w hD) m n u v rho where
  root:=b.root
  P₀:=b.P₀
  torsion:=b.torsion
  twoTorsion:=b.twoTorsion
  shared:=b.shared.toAffineValue
  original:=b.original.toAffineValue
  doubled:=b.doubled.toAffineValue
  slope:=b.slope
  tangent:=b.tangent
  abscissa:=b.abscissa
  ratio:=b.ratio
  sharedDomain:=b.shared.formal_of_reciprocal hp hD
  doubleDomain:=b.doubled.formal_of_reciprocal hp hD

/-- The local scalar divisor on both actual conjugate curves, with the previous
formal-domain and multiplication hypotheses discharged. -/
theorem projective_scalar_divisor {H : Type} [IntModule H] {rho : K}
    (M : ProjectiveGroup ((3-rho)^2) G) (N : ProjectiveGroup ((3-(-rho))^2) H)
    {m n : Int} {r u v q U W b : Rat} (hp : Prime p) (large : 5≤p) (away : p≠17)
    (contact : 0<order p r) (odd : OddOrder (order p r)) (hr : r≠0)
    (values : ScalarValues r u v q U W b) (point : ThreeCoordinates.Sextic (17*b) (289-17*b))
    (left : ProjectiveBranch w M m n u v) (right : ProjectiveBranch w N m n u v)
    (norm : w.incl.map q=left.shared.f*right.shared.f) : ((p^17:Nat):Int)∣n-1 := by
  let dL:=(curve_coeffs w hp large left.root).2.2
  let dR:=(curve_coeffs w hp large right.root).2.2
  exact scalar_index_divisor (M.multiplicationChart w dL) (N.multiplicationChart w dR)
    hp large away contact odd hr values point (left.toScalar hp dL) (right.toScalar hp dR) norm

end ProjectionFibres
