import LocalSupport
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# A number field and a split sextic in one unramified extension

The exceptional primes depend only on the number field. Enlarging the residue
field of a split integral model preserves its root and cluster data. A normal
coefficient field admits an embedding which gives the prescribed sign of the
square root of minus three.
-/

namespace ZOverQ.Qualitative.CommonWittField
open Polynomial IntermediateField IsLocalRing LocalSupport PicardLocal
noncomputable section

/-- Every number field has a power basis whose generator is an algebraic integer. -/
theorem integral_basis_generator (M : Type*) [Field M] [NumberField M] :
    ∃ B : PowerBasis ℚ M, IsIntegral ℤ B.gen := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element ℚ M
  have alg : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ M).mpr
    (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd, hi⟩ := alg.exists_integral_multiple
  let y := d • x
  have heq : ℚ⟮y⟯ = ⊤ := by
    have eqy : y = x * algebraMap ℚ M (d : ℚ) := by simp [y, zsmul_eq_mul, mul_comm]
    rw [eqy, adjoin_simple_mul_algebraMap x (d : ℚ) (by exact_mod_cast hd), hx]
  let B := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := ℚ) y)
  let e := (IntermediateField.equivOfEq heq).trans IntermediateField.topEquiv
  exact ⟨B.map e, by simpa [B, e, PowerBasis.map_gen, IntermediateField.adjoin.powerBasis_gen] using (show IsIntegral ℤ y from hi)⟩

private theorem separable_resultant_ne_zero {P : ℤ[X]}
    (hs : (P.map (algebraMap ℤ ℚ)).Separable) : P.resultant P.derivative ≠ 0 := by
  let j := algebraMap ℤ ℚ
  have inj : Function.Injective j := Int.cast_injective
  have cp : IsCoprime (P.map j) (derivative (P.map j)) := hs
  rw [derivative_map] at cp
  have ne := resultant_ne_zero (P.map j) (P.derivative.map j) cp
  simp only [natDegree_map_eq_of_injective inj, resultant_map_map] at ne
  exact fun eqn => ne (by rw [eqn,map_zero])

set_option maxHeartbeats 1200000 in
/-- A nonzero integral resultant controls all the simple-root conditions for
the same primitive polynomial at every residue characteristic. -/
theorem primitive_polynomial (M : Type*) [Field M] [NumberField M] :
    ∃ (B : PowerBasis ℚ M) (P : ℤ[X]) (N : ℤ) (U V : ℤ[X]),
      P.Monic ∧ P.natDegree ≠ 0 ∧ minpoly ℚ B.gen = P.map (algebraMap ℤ ℚ) ∧
      N ≠ 0 ∧ P * U + P.derivative * V = C N := by
  obtain ⟨B, hi⟩ := integral_basis_generator M
  let P := minpoly ℤ B.gen
  have hm : P.Monic := minpoly.monic hi
  have hp : P.natDegree ≠ 0 := (minpoly.natDegree_pos hi).ne'
  have hq : minpoly ℚ B.gen = P.map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi
  have hsep : (P.map (algebraMap ℤ ℚ)).Separable := hq ▸ Algebra.IsSeparable.isSeparable ℚ B.gen
  let N := P.resultant P.derivative
  have hn : N ≠ 0 := separable_resultant_ne_zero hsep
  obtain ⟨U,V,_,_,h⟩ := exists_mul_add_mul_eq_C_resultant P P.derivative le_rfl le_rfl (Or.inl hp)
  exact ⟨B,P,N,U,V,hm,hp,hq,hn,h⟩

variable (p : ℕ) [Fact p.Prime]

/-- The Witt ring of any of our finite residue extensions has characteristic zero. -/
abbrev wittCharZero (k : Subfield (Residues p)) : CharZero (WittVector p k) :=
  charZero_of_injective_ringHom (f := fromPadics p k)
    ((WittVector.map_injective _ (ZMod.castHom (by simp) k).injective).comp (WittVector.equiv p).symm.injective)

private abbrev residueIso (k : Subfield (Residues p)) [Finite k] :
    ResidueField (WittVector p k) ≃+* k :=
  (Ideal.quotEquivOfEq (show maximalIdeal (WittVector p k) = Ideal.span {(p : WittVector p k)}
    from (WittVector.irreducible p).maximalIdeal_eq)).trans WittVector.quotientPEquiv

private theorem int_comp {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) :
    f.comp (Int.castRingHom S) = Int.castRingHom T := Subsingleton.elim _ _

/-- Adjoin one simple residue root to a given finite residue field, then lift it
to the Witt ring of the enlarged finite field. -/
theorem common_witt_root (F : Subfield (Residues p)) [Finite F]
    {P U V : ℤ[X]} {N : ℤ} (hm : P.Monic) (hp : P.natDegree ≠ 0)
    (bez : P*U + P.derivative*V = C N) (good : (N : ZMod p) ≠ 0) :
    ∃ (k : Subfield (Residues p)) (_ : Finite k), F ≤ k ∧
      ∃ z : WittVector p k, (P.map (Int.castRingHom _)).IsRoot z := by
  let L := Residues p
  let g := Int.castRingHom L
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (P.map g) (by
    rw [hm.degree_map, degree_eq_natDegree hm.ne_zero]
    exact_mod_cast hp)
  have ha0 : P.eval₂ g a = 0 := by simpa only [IsRoot, eval_map] using ha
  have haI : IsIntegral F a := by
    refine ⟨P.map (Int.castRingHom F), hm.map _, ?_⟩
    rw [eval₂_map]
    exact ha0
  let T := IntermediateField.adjoin F ({a} : Set L)
  let k := T.toSubfield
  let : FiniteDimensional F T := IntermediateField.adjoin.finiteDimensional haI
  let : Finite k := Module.finite_of_finite F (M := T)
  let al : k := ⟨a,mem_adjoin_simple_self F a⟩
  have root : P.eval₂ (Int.castRingHom k) al = 0 := by
    apply k.subtype.injective
    rw [Polynomial.hom_eval₂, int_comp, map_zero]
    exact ha0
  have ng : (N:k) ≠ 0 := by
    have j := (ZMod.castHom (by simp) k).injective.ne good
    simpa using j
  have der : P.derivative.eval₂ (Int.castRingHom k) al ≠ 0 := by
    intro h
    have t := congrArg (eval₂ (Int.castRingHom k) al) bez
    simp only [eval₂_add,eval₂_mul,root,h,zero_mul,add_zero,eval₂_C] at t
    exact ng t.symm
  let S := WittVector p k
  let : HenselianRing S (maximalIdeal S) := by
    rw [(show Irreducible (p:S) from WittVector.irreducible p).maximalIdeal_eq]
    infer_instance
  let i := (residueIso p k).symm
  let r := i al
  have h₁ : (P.map (Int.castRingHom S)).eval₂ (residue S) r = 0 := by
    rw [eval₂_map]
    have hl : i.toRingHom (P.eval₂ (Int.castRingHom k) al) = 0 := by rw [root,map_zero]
    rw [Polynomial.hom_eval₂,int_comp] at hl
    rwa [int_comp]
  have h₂ : (P.map (Int.castRingHom S)).derivative.eval₂ (residue S) r ≠ 0 := by
    rw [derivative_map,eval₂_map]
    have hl : i.toRingHom (P.derivative.eval₂ (Int.castRingHom k) al) ≠ 0 :=
      (map_ne_zero_iff _ i.injective).mpr der
    rw [Polynomial.hom_eval₂,int_comp] at hl
    rwa [int_comp]
  obtain ⟨z,hz,_⟩ := ZInQBlueprint.HenselTriples.liftSimple _ r h₁ h₂
  exact ⟨k,inferInstance,fun b hb => T.algebraMap_mem (⟨b,hb⟩ : F),z,hz⟩

/-- A single finite set of primes works for every initial finite residue field. -/
theorem number_field_embedding (M : Type*) [Field M] [NumberField M] :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime], (N : ZMod p) ≠ 0 →
      ∀ F : Subfield (Residues p), ∀ [Finite F],
        ∃ (k : Subfield (Residues p)) (_ : Finite k), F ≤ k ∧
          letI := wittCharZero p k
          Nonempty (M →ₐ[ℚ] FractionRing (WittVector p k)) := by
  obtain ⟨B,P,N,U,V,hm,hp,hq,hn,bez⟩ := primitive_polynomial M
  refine ⟨N, hn, fun p _ good F _ => ?_⟩
  obtain ⟨k,fin,hF,z,hz⟩ := common_witt_root p F hm hp bez good
  let := wittCharZero p k
  let S := WittVector p k
  let K := FractionRing S
  let w := algebraMap S K z
  have hw : aeval w (minpoly ℚ B.gen) = 0 := by
    rw [hq,aeval_def,eval₂_map]
    have h₀ : P.eval₂ (Int.castRingHom S) z = 0 := by simpa only [IsRoot,eval_map] using hz
    have ht := congrArg (algebraMap S K) h₀
    rw [Polynomial.hom_eval₂, int_comp, map_zero] at ht
    rwa [show (algebraMap ℚ K).comp (algebraMap ℤ ℚ) = Int.castRingHom K from Subsingleton.elim _ _]
  exact ⟨k,fin,hF,⟨B.lift w hw⟩⟩

/-- Normality permits either sign at the specified quadratic subfield. -/
theorem marked_embedding {M K : Type*} [Field M] [NumberField M] [Normal ℚ M]
    [Field K] [CharZero K] (δ : M) (q : K) (hδ : δ^2 = -3) (hq : q^2 = -3)
    (j : M →ₐ[ℚ] K) : ∃ i : M →ₐ[ℚ] K, i δ = q := by
  have h : (j δ)^2 = q^2 := by rw [← map_pow,hδ,map_neg,map_ofNat,hq]
  obtain hj|hj := sq_eq_sq_iff_eq_or_eq_neg.mp h
  · exact ⟨j,hj⟩
  let P : ℚ[X] := X^2+C 3
  have deg : P.natDegree = 2 := by dsimp [P]; compute_degree!
  have irr : Irreducible P := irreducible_of_degree_le_three_of_not_isRoot (by rw [deg]; decide) (by
    intro a ha
    have t : a^2+3=0 := by simpa [P,IsRoot] using ha
    nlinarith [sq_nonneg a])
  have mp : minpoly ℚ δ = P :=
    (minpoly.eq_of_irreducible_of_monic irr (by simp [P,hδ]) (monic_X_pow_add_C (3:ℚ) (by decide : 2≠0))).symm
  obtain ⟨σ,hs⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) δ)
    (x := -δ) (by rw [mp]; simp [P,hδ])
  exact ⟨j.comp σ.toAlgHom, by simp [hs,hj]⟩

/-- Extension of the finite residue field leaves the strict Witt roots fixed. -/
def extendSplitting {a b e : ℤ} {q : WittRing p} (D : FiniteSplitting p a b e q)
    (k : Subfield (Residues p)) [Finite k] (sub : D.field ≤ k) : FiniteSplitting p a b e q := by
  let i : WittVector p D.field →+* WittVector p k := WittVector.map (Subfield.inclusion sub)
  have comp (x : WittVector p D.field) : inclusion p k (i x) = inclusion p D.field x := by
    ext j
    rfl
  exact {
    field := k
    finite := inferInstance
    rho := i D.rho
    inclusion_rho := (comp D.rho).trans D.inclusion_rho
    radical := fun z h => by
      obtain ⟨v,hv⟩ := D.radical z h
      exact ⟨i v,(comp v).trans hv⟩
    splits := by
      have h := D.splits.map i
      simpa [twisted,upper,lower,sextic_map,map_ofNat] using h
  }

/-- The actual DDMM fibre data, including root labels and principal-cluster
parities, can use the enlarging residue field. -/
def extendFibre {a b e : ℤ} {q : WittRing p} {A : Finset (Fin 2)} {m : ℕ}
    (D : FibreData p a b e q A m) (k : Subfield (Residues p)) [Finite k]
    (sub : D.finiteModel.field ≤ k) : FibreData p a b e q A m :=
  { D with finiteModel := extendSplitting p D.finiteModel k sub }

/-- Away from the prime divisors of one integer depending only on the normal
number field, the same finite unramified Witt model carries the split sextic
and a field embedding with the prescribed value of the distinguished radical. -/
theorem common_marked_fibre (M : Type*) [Field M] [NumberField M] [Normal ℚ M]
    (δ : M) (hδ : δ^2 = -3) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime], (N : ZMod p) ≠ 0 →
      ∀ {a b e : ℤ} {q : WittRing p} {A : Finset (Fin 2)} {m : ℕ}, q^2 = -3 →
      ∀ D : FibreData p a b e q A m, ∃ D' : FibreData p a b e q A m,
        D.finiteModel.field ≤ D'.finiteModel.field ∧ D'.roots = D.roots ∧
        let S := WittVector p D'.finiteModel.field
        letI := wittCharZero p D'.finiteModel.field
        ∃ i : M →ₐ[ℚ] FractionRing S, i δ = algebraMap S (FractionRing S) D'.finiteModel.rho := by
  obtain ⟨N,hn,emb⟩ := number_field_embedding M
  refine ⟨N, hn, ?_⟩
  intro p inst good a b e q A m hq D
  let := D.finiteModel.finite
  obtain ⟨k,fin,sub,⟨i⟩⟩ := emb p good D.finiteModel.field
  let D' := extendFibre p D k sub
  refine ⟨D', sub, rfl, ?_⟩
  let S := WittVector p k
  let K := FractionRing S
  let := wittCharZero p k
  let r : S := WittVector.map (Subfield.inclusion sub) D.finiteModel.rho
  change ∃ i : M →ₐ[ℚ] K, i δ = algebraMap S K r
  have hr₀ : D.finiteModel.rho^2 = -3 := by
    apply inclusion_injective p D.finiteModel.field
    rw [map_pow, D.finiteModel.inclusion_rho, hq, map_neg, map_ofNat]
  have hr : r^2 = -3 := by
    dsimp only [r]
    rw [← map_pow,hr₀,map_neg,map_ofNat]
  exact marked_embedding δ _ hδ (by rw [← map_pow, hr, map_neg, map_ofNat]) i

end
end ZOverQ.Qualitative.CommonWittField

#print axioms ZOverQ.Qualitative.CommonWittField.primitive_polynomial
#print axioms ZOverQ.Qualitative.CommonWittField.common_witt_root
#print axioms ZOverQ.Qualitative.CommonWittField.number_field_embedding
#print axioms ZOverQ.Qualitative.CommonWittField.marked_embedding

#print axioms ZOverQ.Qualitative.CommonWittField.common_marked_fibre
