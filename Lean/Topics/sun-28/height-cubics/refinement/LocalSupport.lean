import MarkedFrey

namespace Sun28.HeightCubics.Refinement
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK
open private away_support from RowPool
noncomputable section

private theorem prime_int {p:ℕ} (hp:p.Prime) : Prime (p:ℤ) := by
  simpa [Int.prime_iff_natAbs_prime] using hp

private theorem factor_mem {p:ℕ} (hp:p.Prime) {z:ℤ} (nz:z≠0) (dv:(p:ℤ)∣z) :
    p∈z.natAbs.primeFactors := Nat.mem_primeFactors.mpr
  ⟨hp,by simpa using Int.natAbs_dvd_natAbs.mpr dv,Int.natAbs_ne_zero.mpr nz⟩

private theorem large_prime {A B:ℤ} {p:ℕ} (hp:p.Prime) (out:p∉support A B) : 1728<p := by
  by_contra h
  exact out (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩))

private theorem no_constant {p:ℕ} {n:ℤ} (nonzero:n≠0) (lt:n.natAbs<p) : ¬(p:ℤ)∣n := by
  intro h
  have hd:p∣n.natAbs:=by simpa using Int.natAbs_dvd_natAbs.mpr h
  exact (not_lt_of_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) hd)) lt

/-- At an unseen prime all the two zero-invariant tests for the integral
curve reduce to membership of the two visible rows. -/
theorem local_tests (r:ThreeRows) {A B u:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (sq:left r A B=sqfInt (left r A B)*u^2)
    {p:ℕ} (hp:p.Prime) (out:p∉support A B) :
    let P:=left r A B
    let Q:=right r A B
    let E:=frey (sqfInt P) (cubePart Q) u (cubeRoot Q)
    ((p:ℤ)∣E.Δ → p∈defective r.b A B ∨ p∈residualMark A B r.center) ∧
    (p∈residualMark A B r.center → (p:ℤ)∣E.Δ ∧ ¬(p:ℤ)∣E.c₄) := by
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
  have a144:=no_constant (n:=(-144:ℤ)) (by decide) (lt_trans (by decide:(-144:ℤ).natAbs<1728) (large_prime hp out))
  have a1728:=no_constant (n:=(-1728:ℤ)) (by decide) (large_prime hp out)
  change ((p:ℤ)∣(frey d e u v).Δ → _) ∧ (_ → (p:ℤ)∣(frey d e u v).Δ ∧ _)
  constructor
  · intro w
    rw [delta] at w
    have mixed:p∈mixedPlaces P Q R:=by
      rcases pr.dvd_mul.mp w with z|z
      · rcases pr.dvd_mul.mp z with z|z
        · have one:=(pr.dvd_mul.mp z).resolve_left a1728
          exact Finset.mem_union_left _ (factor_mem hp dn (pr.dvd_of_dvd_pow one))
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (coeff_primes qn (factor_mem hp en (pr.dvd_of_dvd_pow z))))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (factor_mem hp rn z))
    exact Finset.mem_union.mp ((exact_hidden r off) ▸ Finset.mem_sdiff.mpr ⟨mixed,out⟩)
  · intro center
    obtain ⟨c,_⟩:=Finset.mem_sdiff.mp center
    have cb:(p:ℤ)∣oldForm r.center A B:=Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors c)
    have noP:¬(p:ℤ)∣P:=by
      intro dv
      have row:=away_support out r.ib (off r.a) (factor_mem hp pn dv)
      exact r.ia (unique_form cop (fun w=>out (Finset.mem_union_left _ w)) c (Finset.mem_sdiff.mp row).1)
    have noQ:¬(p:ℤ)∣Q:=by
      intro dv
      have row:=away_support out r.ia.symm (off r.b) (factor_mem hp qn dv)
      exact r.ib (unique_form cop (fun w=>out (Finset.mem_union_left _ w)) c (Finset.mem_sdiff.mp row).1)
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
end Sun28.HeightCubics.Refinement
#print axioms Sun28.HeightCubics.Refinement.local_tests
