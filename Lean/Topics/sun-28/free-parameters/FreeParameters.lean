import PoleParameters
import CompiledEndpoint

/-! The continuous coordinates of the certificate, in the order of Sun §8. -/
namespace Sun28.Forward
open Sun28.WitnessIndices Sun28.Ordinary Sun28.ScalarHeight ZInQ
noncomputable section

/-- U[0..17] are the two components of the nine abscissae. U[18] is η.
U[19..24] are the three ordinary pole pairs. U[25..26] are the scalar pole pair. -/
def FreeTests (u : Fin 27 → ℚ) (A : Fin 9 → AffineInput) (M : ℕ) (c : ℤ)
    (x Γ : ℚ) (D : ℕ) (Uo Us : Finset ℚ) : Prop :=
  let w := (nineAffine A).doubles
  (∀ i, (A i).re=u ⟨2*i.val,by omega⟩ ∧ (A i).im=u ⟨2*i.val+1,by omega⟩) ∧
  w.Q≠0 ∧ w.H≠0 ∧ translatedBase w c≠0 ∧
  RationalOddChart w.N ∧ RationalOddChart w.T ∧ RationalOddChart w.Z ∧
  (∀ j, (pointScale w M j)^2*u 18 ∉ marks ∧ (pointScale w M j)^2*u 18≠3 ∧ pointScale w M j≠0) ∧
  (∀ j, let s:=pointScale w M j
    ordinaryAtPair w M c (beta x) (s^2) (s^2*u 18) Uo
      (u ⟨19+2*j.val,by omega⟩) (u ⟨20+2*j.val,by omega⟩)) ∧
  scalarAtPair w M (scalarRadicand (beta x)) Γ D Us (u 25) (u 26)

theorem free_tests_certificate {u A M c x Γ D Uo Us} (f : FreeTests u A M c x Γ D Uo Us) :
    PointCertificate (nineAffine A).doubles M c x (u 18) Γ D Uo Us := by
  obtain ⟨_,q,h,b,n,t,z,g,ord,sc⟩ := f
  exact ⟨q,h,b,n,t,z,g,fun j => (ordinary_parameters ..).2 ⟨_,_,ord j⟩,(scalar_parameters ..).2 ⟨_,_,sc⟩⟩

private def pack (A : Fin 9 → AffineInput) (η : ℚ) (e z : Fin 3 → ℚ) (s t : ℚ) (i : Fin 27) : ℚ :=
  if left : i.val < 18 then
    let a := A ⟨i.val/2,by omega⟩
    if i.val%2=0 then a.re else a.im
  else if i.val=18 then η
  else if middle : i.val <25 then
    let j : Fin 3 := ⟨(i.val-19)/2,by omega⟩
    if i.val%2=1 then e j else z j
  else if i.val=25 then s else t

/-- Prescribing the nine affine records and η leaves exactly the three ordinary
pole pairs and one scalar pair to insert in the specified continuous coordinates. -/
theorem certificate_free_tests (A M c x η Γ D Uo Us)
    (p : PointCertificate (nineAffine A).doubles M c x η Γ D Uo Us) :
    ∃ u : Fin 27 → ℚ, u 18=η ∧ FreeTests u A M c x Γ D Uo Us := by
  classical
  have choices := fun j => (ordinary_parameters ..).1 (p.ordinary j)
  choose e z ord using choices
  obtain ⟨s,t,sc⟩ := (scalar_parameters ..).1 p.scalar
  let u := pack A η e z s t
  have slope : u 18=η := rfl
  refine ⟨u,slope,?_,p.q_nonzero,p.h_nonzero,p.base_nonzero,p.odd_N,p.odd_T,p.odd_Z,?_,?_,?_⟩
  · intro i
    fin_cases i <;> exact ⟨rfl,rfl⟩
  · simpa only [slope] using p.scale_guard
  · intro j
    fin_cases j <;> first | exact ord 0 | exact ord 1 | exact ord 2
  · exact sc

/-- This relation has the 28 base coordinates of the compiler, input first. -/
def parameterRelation (c : ℤ) (Γ : ℚ) (D : ℕ) (Uo Us : Finset ℚ) (p : Fin 28 → ℚ) : Prop :=
  ∃ A : Fin 9 → AffineInput, FreeTests (fun j => p j.succ) A
    (forwardMultiplier (commonCutoff c Γ Uo Us)) c (p 0) Γ D Uo Us

/-- Simultaneous rational witnesses for every integer, with the same fixed constants. -/
def IntegerWitnesses (c : ℤ) (Γ : ℚ) (D : ℕ) (Uo Us : Finset ℚ) : Prop :=
  ∀ k : ℤ, ∃ u : Fin 27 → ℚ, parameterRelation c Γ D Uo Us (Fin.cases (k:ℚ) u)

theorem integer_witnesses_iff (c Γ D Uo Us) :
    IntegerWitnesses c Γ D Uo Us ↔ ∀ k : ℤ, ∃ A : Fin 9 → AffineInput, ∃ η : ℚ,
      PointCertificate (nineAffine A).doubles (forwardMultiplier (commonCutoff c Γ Uo Us))
        c (k:ℚ) η Γ D Uo Us := by
  constructor
  · intro ch k
    obtain ⟨u,A,p⟩ := ch k
    exact ⟨A,u 18,free_tests_certificate p⟩
  · intro ch k
    obtain ⟨A,η,p⟩ := ch k
    obtain ⟨u,_,f⟩ := certificate_free_tests _ _ _ _ _ _ _ _ _ p
    exact ⟨u,A,f⟩

theorem parameter_sound {c Γ D Uo Us p} (cn : c≠0) (gn : Γ≠0)
    (chart : OrdinaryCharts (commonCutoff c Γ Uo Us) K0)
    (five : OriginalFiveHeight glazerConstant24 oldCutoff)
    (h : parameterRelation c Γ D Uo Us p) : ∃ k : ℤ, p 0=(k:ℚ) := by
  obtain ⟨A,f⟩ := h
  obtain ⟨k,e,_⟩ := rational_witness_sound A c (p 0) (p 19) Γ D Uo Us cn gn chart five (free_tests_certificate f)
  exact ⟨k,e⟩

/-- Exact two-sided specialization required of the list of monic systems.
The equality is at each fixed 28-tuple, before projecting away any parameter. -/
def ExactBranchList (c : ℤ) (Γ : ℚ) (D : ℕ) (Uo Us : Finset ℚ)
    (bs : List (Sun28.Compiler.Branch 28)) : Prop :=
  ∀ p : Fin 28 → ℚ, (∃ b ∈ bs, Sun28.Compiler.Solutions b.tower b.equations b.guards p) ↔
    parameterRelation c Γ D Uo Us p

/-- A guarded implementation may reject additional exceptional tuples. Its soundness
only requires decoding each successful branch at its given parameter tuple. -/
def BranchesDecode (c : ℤ) (Γ : ℚ) (D : ℕ) (Uo Us : Finset ℚ)
    (bs : List (Sun28.Compiler.Branch 28)) : Prop :=
  ∀ p : Fin 28 → ℚ, (∃ b ∈ bs, Sun28.Compiler.Solutions b.tower b.equations b.guards p) →
    parameterRelation c Γ D Uo Us p

private theorem compiled_branch_iff (bs : List (Sun28.Compiler.Branch 28)) (x : ℚ) :
    (∃ y : Fin 28 → ℚ, Sun28.eval28 (Sun28.Branches.polynomial28 (Sun28.Compiler.branchAtlas bs)) x y=0) ↔
      Sun28.Compiler.branchRelation bs x := by
  rw [Sun28.Branches.polynomial28_spec]
  exact exists_congr fun _ => Sun28.Compiler.branchAtlas_spec ..

theorem compiled_projection_of_decoding {c Γ D Uo Us} (cn : c≠0) (gn : Γ≠0)
    (chart : OrdinaryCharts (commonCutoff c Γ Uo Us) K0)
    (five : OriginalFiveHeight glazerConstant24 oldCutoff)
    (bs : List (Sun28.Compiler.Branch 28)) (decode : BranchesDecode c Γ D Uo Us bs)
    (complete : ∀ k : ℤ, Sun28.Compiler.branchRelation bs (k:ℚ)) (x : ℚ) :
    (∃ y : Fin 28 → ℚ, Sun28.eval28 (Sun28.Branches.polynomial28 (Sun28.Compiler.branchAtlas bs)) x y=0) ↔
      ∃ k : ℤ, x=(k:ℚ) := by
  rw [compiled_branch_iff]
  constructor
  · rintro ⟨u,h⟩
    exact parameter_sound cn gn chart five (decode _ h)
  · rintro ⟨k,rfl⟩
    exact complete k

attribute [local irreducible] FreeTests parameterRelation Sun28.Compiler.branchAtlas
  Sun28.Branches.polynomial28 Sun28.eval28 in
/-- The actual polynomial produced by the compiler defines the integers if
the pointwise branch equivalence and the simultaneous integer witnesses are supplied. -/
theorem compiled_point_projection {c Γ D Uo Us} (cn : c≠0) (gn : Γ≠0)
    (chart : OrdinaryCharts (commonCutoff c Γ Uo Us) K0)
    (five : OriginalFiveHeight glazerConstant24 oldCutoff)
    (bs : List (Sun28.Compiler.Branch 28)) (branches : ExactBranchList c Γ D Uo Us bs)
    (complete : IntegerWitnesses c Γ D Uo Us) (x : ℚ) :
    (∃ y : Fin 28 → ℚ, Sun28.eval28 (Sun28.Branches.polynomial28 (Sun28.Compiler.branchAtlas bs)) x y=0) ↔
      ∃ k : ℤ, x=(k:ℚ) := by
  apply compiled_projection_of_decoding cn gn chart five bs (fun p => (branches p).1) _ x
  intro k
  obtain ⟨u,h⟩ := complete k
  exact ⟨u,(branches _).2 h⟩

end
end Sun28.Forward
#print axioms Sun28.Forward.free_tests_certificate
#print axioms Sun28.Forward.certificate_free_tests
#print axioms Sun28.Forward.parameter_sound
#print axioms Sun28.Forward.compiled_point_projection

#print axioms Sun28.Forward.integer_witnesses_iff

#print axioms Sun28.Forward.compiled_projection_of_decoding
