import ConductorBudget

/-! The three different prime supports of an ordered five-mark chart. -/
namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres ZInQ.RouteK Refinement
open private kernel_primes from SignedSupport
noncomputable section

def baseSet (i:Fin 5) (A B:ℤ) : Finset ℕ := formPrimes i A B \ core
def order (i:Fin 5) (A B:ℤ) (p:ℕ) : ℕ := (oldForm i A B).natAbs.factorization p
def squareSet (i:Fin 5) (A B:ℤ) := (baseSet i A B).filter fun p=>order i A B p%2=1
def cubeSet (i:Fin 5) (A B:ℤ) := (baseSet i A B).filter fun p=>order i A B p%3≠0

private theorem prime_int {p:ℕ} (hp:p.Prime) : Prime (p:ℤ) := by
  simpa [Int.prime_iff_natAbs_prime] using hp

private theorem factor_mem {p:ℕ} (hp:p.Prime) {z:ℤ} (nz:z≠0) (dv:(p:ℤ)∣z) :
    p∈z.natAbs.primeFactors := Nat.mem_primeFactors.mpr
  ⟨hp,by simpa using Int.natAbs_dvd_natAbs.mpr dv,Int.natAbs_ne_zero.mpr nz⟩

private theorem row_mem {z a:ℤ} {j k i:Fin 5} {p:ℕ} (away:p∉core) (jk:j≠k)
    (off:oldForm i z a≠0) (dv:p∈(det j k*oldForm i z a).natAbs.primeFactors) :
    p∈baseSet i z a := by
  rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr (det_ne jk)) (Int.natAbs_ne_zero.mpr off)] at dv
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp dv).resolve_left (fun m=>away (minor_support _ _ m)),away⟩

private theorem row_order {A B:ℤ} {j k i:Fin 5} {p:ℕ} (hp:p.Prime) (away:p∉core) (jk:j≠k)
    (off:oldForm i A B≠0) :
    (det j k*oldForm i A B).natAbs.factorization p=order i A B p := by
  have nd:¬p∣(det j k).natAbs:=fun d=>away (minor_support _ _ (Nat.mem_primeFactors.mpr
    ⟨hp,d,Int.natAbs_ne_zero.mpr (det_ne jk)⟩))
  rw [Int.natAbs_mul,Nat.factorization_mul (Int.natAbs_ne_zero.mpr (det_ne jk)) (Int.natAbs_ne_zero.mpr off),
    Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd nd,zero_add]
  rfl

private theorem exclude_six {p:ℕ} (hp:p.Prime) (away:p∉core) {n:ℤ} (fact:n.natAbs∣210^8) :
    ¬(p:ℤ)∣n := by
  intro dv
  have d:p∣n.natAbs:=by simpa using Int.natAbs_dvd_natAbs.mpr dv
  exact away (Nat.mem_primeFactors.mpr ⟨hp,hp.dvd_of_dvd_pow (d.trans fact),by decide⟩)

theorem local_roles (r:ThreeRows) {A B u:ℤ} (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0)
    (sq:left r A B=sqfInt (left r A B)*u^2) {p:ℕ} (hp:p.Prime) (away:p∉core) :
    let P:=left r A B
    let Q:=right r A B
    let E:=frey (sqfInt P) (cubePart Q) u (cubeRoot Q)
    ((p:ℤ)∣E.Δ → p∈squareSet r.a A B ∨ p∈cubeSet r.b A B ∨ p∈baseSet r.center A B) ∧
    (p∈baseSet r.center A B → (p:ℤ)∣E.Δ ∧ ¬(p:ℤ)∣E.c₄) := by
  let P:=left r A B
  let Q:=right r A B
  let R:=baseRow r A B
  let d:=sqfInt P
  let e:=cubePart Q
  let v:=cubeRoot Q
  have pn:P≠0:=mul_ne_zero (det_ne r.ib) (off _)
  have qn:Q≠0:=mul_ne_zero (det_ne r.ia.symm) (off _)
  have rn:R≠0:=mul_ne_zero (det_ne r.ab) (off _)
  have qeq:Q=e*v^3:=factor_cube qn
  have he:d*u^2+e*v^3=R:=by rw [←sq,←qeq];exact minor_identity _ _ _ A B
  have pr:=prime_int hp
  have dn:d≠0:=(sqfInt_spec pn).1.ne_zero
  have en:e≠0:=fun h=>qn (by rw [qeq,h,zero_mul])
  have delta:(frey d e u v).Δ= -1728*d^3*e^2*R:=by rw [frey_discriminant,he]
  have a144:=exclude_six (n:=(-144:ℤ)) hp away (by decide)
  have a1728:=exclude_six (n:=(-1728:ℤ)) hp away (by decide)
  change ((p:ℤ)∣(frey d e u v).Δ → _) ∧ (_ → (p:ℤ)∣(frey d e u v).Δ ∧ _)
  constructor
  · intro bad
    rw [delta] at bad
    rcases pr.dvd_mul.mp bad with de|dd
    · rcases pr.dvd_mul.mp de with dd|ee
      · have mem:=factor_mem hp dn (pr.dvd_of_dvd_pow ((pr.dvd_mul.mp dd).resolve_left a1728))
        change p∈(sqfInt P).natAbs.primeFactors at mem
        rw [kernel_primes pn] at mem
        have odd:=(Finset.mem_filter.mp mem).2
        rw [padicValInt,←Nat.factorization_def _ hp] at odd
        change Odd ((det r.center r.b*oldForm r.a A B).natAbs.factorization p) at odd
        rw [row_order hp away r.ib (off _)] at odd
        exact Or.inl (Finset.mem_filter.mpr ⟨row_mem away r.ib (off _) (Finset.mem_filter.mp mem).1,
          by obtain ⟨k,hk⟩:=odd;omega⟩)
      · obtain ⟨mem,frac⟩:=Finset.mem_filter.mp (coeff_primes qn (factor_mem hp en (pr.dvd_of_dvd_pow ee)))
        change (det r.a r.center*oldForm r.b A B).natAbs.factorization p%3≠0 at frac
        rw [row_order hp away r.ia.symm (off _)] at frac
        exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨row_mem away r.ia.symm (off _) mem,frac⟩))
    · exact Or.inr (Or.inr (row_mem away r.ab (off _) (factor_mem hp rn dd)))
  · intro center
    have c: p∈formPrimes r.center A B:=(Finset.mem_sdiff.mp center).1
    have cb:(p:ℤ)∣oldForm r.center A B:=Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors c)
    have noP:¬(p:ℤ)∣P:=by
      intro dv
      exact r.ia (unique_mark cop away c (Finset.mem_sdiff.mp (row_mem away r.ib (off _) (factor_mem hp pn dv))).1)
    have noQ:¬(p:ℤ)∣Q:=by
      intro dv
      exact r.ib (unique_mark cop away c (Finset.mem_sdiff.mp (row_mem away r.ia.symm (off _) (factor_mem hp qn dv))).1)
    have dr:(p:ℤ)∣R:=dvd_mul_of_dvd_right cb _
    refine ⟨delta ▸ dvd_mul_of_dvd_right dr _,?_⟩
    rw [frey_c4]
    intro dv
    rcases pr.dvd_mul.mp dv with de|vv
    · rcases pr.dvd_mul.mp de with dd|ee
      · exact noP (((pr.dvd_mul.mp dd).resolve_left a144).trans ⟨u^2,sq⟩)
      · exact noQ (ee.trans (part_dvd qn))
    · exact noQ (vv.trans (root_dvd qn))

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.local_roles
