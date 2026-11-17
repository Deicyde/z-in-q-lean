import ScalarCharts

namespace StructuralReduction
open Lean.Grind WitnessTransfer BinaryQuartic ProgressionWitnesses.SingleContact
attribute [local instance] Semiring.natCast Ring.intCast

variable {p : Nat} {K : Type} [Field K] {w : ExtensionPlace p K}
variable {G : Type} [IntModule G] (chart : MultiplicationChart p w G)

/-- A branch consists of physical affine coordinates at the source points, with
the tangent at R. The two formal-domain tests are the reciprocal-x criterion
at infinity. The multiplier tangent law is specified separately by the chart. -/
structure ScalarBranch (m n : Int) (u v : Rat) (rho : K) where
  root : rho^2=2
  P₀ : G
  torsion : G
  twoTorsion : (2:Int) • torsion=0
  shared : AffineValue ((3-rho)^2) (chart.z (m • P₀+torsion))
  original : AffineValue ((3-rho)^2) (chart.z ((n-1) • ((2:Int) • P₀)))
  doubled : AffineValue ((3-rho)^2) (chart.z ((2:Int) • ((n-1) • ((2:Int) • P₀))))
  slope : K
  tangent : 2*original.y*slope=3*original.x^2-(3-rho)^2
  abscissa : doubled.x=slope^2-2*original.x
  ratio : chart.z ((n-1) • ((2:Int) • P₀))=
    chart.z (m • P₀+torsion)*(w.incl.map u+w.incl.map v*rho)
  sharedDomain : 0<w.val shared.f → chart.formal (m • P₀+torsion)
  doubleDomain : 0<w.val doubled.f → chart.formal ((2:Int) • ((n-1) • ((2:Int) • P₀)))

private theorem lift_depth {a : Rat} (h : a≠0 → 17≤order p a) : w.deep 17 (w.incl.map a) := by
  intro ne
  have az : a≠0 := fun z=>ne (by rw [z,w.incl.zero])
  rw [(w.agrees a az).2];exact h az

theorem ScalarBranch.divides {m n : Int} {u v : Rat} {rho : K} (b : ScalarBranch chart m n u v rho)
    (hp : Prime p) (large : 5≤p) (high : 8<w.val b.shared.f)
    (hu : u≠0 → 17≤order p u) (hv : v≠0 → 17≤order p v) : ((p^17:Nat):Int)∣n-1 := by
  let H:=m • b.P₀+b.torsion
  let R:=(n-1) • ((2:Int) • b.P₀)
  obtain ⟨rn,vr,d⟩:=curve_coeffs w hp large b.root
  have fz:=formal_parameter w hp d b.shared (by omega)
  change w.val b.shared.f=2*w.val (chart.z H) at fz
  have zd : 2≤w.val (chart.z H) := by omega
  have second : w.deep 17 (w.incl.map v*rho) := by
    intro prod
    have vn : w.incl.map v≠0 := fun z=>prod (by rw [z,Semiring.zero_mul])
    have deep:=lift_depth (w:=w) hv vn
    rw [w.mul _ _ vn rn,vr,Int.add_zero];exact deep
  have both:=w.deep_add (lift_depth (w:=w) hu) second
  have eq : chart.z R=chart.z H*(w.incl.map u+w.incl.map v*rho) := b.ratio
  have sumNonzero : w.incl.map u+w.incl.map v*rho≠0 := fun z=>b.original.live.2.2 (by rw [eq,z,Semiring.mul_zero])
  have depth:=both sumNonzero
  have ratioOrd:=w.mul _ _ b.shared.live.2.2 sumNonzero
  change w.val (chart.z H*(w.incl.map u+w.incl.map v*rho))=_ at ratioOrd
  rw [←eq] at ratioOrd
  change w.val (chart.z R)=w.val (chart.z H)+w.val (w.incl.map u+w.incl.map v*rho) at ratioOrd
  have rz : 0<w.val (chart.z R) := by omega
  obtain ⟨df,dup⟩:=double_parameter w hp large d b.original b.doubled _ b.tangent b.abscissa rz
  apply index_divisor chart hp large (scalar_group_identity m n b.P₀ b.torsion b.twoTorsion)
    (b.sharedDomain (by omega)) b.shared.live.2.2 zd (b.doubleDomain df) b.doubled.live.2.2
  change w.val (chart.z H)+17≤w.val (chart.z ((2:Int) • R))
  change w.val (chart.z ((2:Int) • R))=w.val (chart.z R) at dup
  omega

/-- From a single physical scalar and both conjugate evaluations, select the deep
reference using q=f(H)f(H'). Conjugation may act within one local field (inert case).
The root, index, and rational coefficients are shared across the two evaluations. -/
theorem scalar_index_divisor {G' : Type} [IntModule G'] (other : MultiplicationChart p w G')
    {m n : Int} {r u v q U W b : Rat} {rho : K} (hp : Prime p) (large : 5≤p) (away : p≠17)
    (contact : 0<order p r) (odd : OddOrder (order p r)) (hr : r≠0)
    (values : ScalarValues r u v q U W b) (point : ThreeCoordinates.Sextic (17*b) (289-17*b))
    (left : ScalarBranch chart m n u v rho) (right : ScalarBranch other m n u v (-rho))
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
  · exact left.divides chart hp large h highU highV
  · exact right.divides other hp large (by omega) highU highV

end StructuralReduction
