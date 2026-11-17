import RootField

/-! Inertia at a prime prime to the two defining squareclasses. -/
namespace Sun28.FiveDescent.ResidueField
open NumberField IntermediateField
open scoped NumberField
noncomputable section

theorem inertia_root {L : Type*} [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (σ : L ≃ₐ[ℚ] L) (inertia : σ∈P.inertia (L ≃ₐ[ℚ] L)) {a : ℤ} {u : 𝓞 L}
    (root : u^2=(a:𝓞 L)) (two : (2:𝓞 L)∉P) (unit : (a:𝓞 L)∉P) :
    σ (u:L)=(u:L) := by
  have v : (σ • u)^2=u^2 := by
    apply Subtype.ext
    change (σ (u:L))^2=(u:L)^2
    have h : (u:L)^2=(a:L) := congrArg (fun z : 𝓞 L => (z:L)) root
    rw [←map_pow,h,map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp v with eq|eq
  · exact congrArg (fun z : 𝓞 L => (z:L)) eq
  · have h := Ideal.mem_inertia.mp inertia u
    rw [eq] at h
    have h' : (2:𝓞 L)*u∈P := by
      convert P.neg_mem h using 1; ring
    have um := ((inferInstance : P.IsPrime).mem_or_mem h').resolve_left two
    exact False.elim (unit (root ▸ P.pow_mem_of_mem um 2 (by decide)))

theorem inertia_trivial {d e : ℤ} {r w : Omega} (hr:r^2=(d:Omega)) (hw:w^2=(e:Omega))
    (P : Ideal (𝓞 (coords r w))) [P.IsPrime]
    (two : (2:𝓞 (coords r w))∉P) (dunit : (d:𝓞 (coords r w))∉P)
    (eunit : (e:𝓞 (coords r w))∉P) :
    P.inertia (coords r w ≃ₐ[ℚ] coords r w)=⊥ := by
  apply le_antisymm _ bot_le
  intro σ hσ
  rw [Subgroup.mem_bot]
  let rL := AdjoinPair.gen₁ ℚ r w
  let wL := AdjoinPair.gen₂ ℚ r w
  have hv : rL^2=(d:coords r w) := Subtype.ext (by simpa [rL,AdjoinPair.gen₁] using hr)
  have ht : wL^2=(e:coords r w) := Subtype.ext (by simpa [wL,AdjoinPair.gen₂] using hw)
  let ir : 𝓞 (coords r w) := ⟨rL,integral_root hv⟩
  let iw : 𝓞 (coords r w) := ⟨wL,integral_root ht⟩
  have a := inertia_root P σ hσ (u:=ir) (a:=d) (Subtype.ext hv) two dunit
  have b := inertia_root P σ hσ (u:=iw) (a:=e) (Subtype.ext ht) two eunit
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext
  intro z hz
  rcases Set.mem_insert_iff.mp hz with v|v
  · subst z; exact a
  · rw [Set.mem_singleton_iff] at v; subst z; exact b

/-- An odd prime away from both radicands is unramified in the actual
compositum, independently of the degrees of its two generators. -/
theorem prime_not_dvd_discr {d e : ℤ} {r w : Omega} (hr:r^2=(d:Omega)) (hw:w^2=(e:Omega))
    {p : ℕ} (pr : p.Prime) (odd : p≠2) (hd : ¬(p:ℤ)∣d) (he : ¬(p:ℤ)∣e) :
    ¬(p:ℤ)∣NumberField.discr (coords r w) := by
  let L := coords r w
  let : IsGalois ℚ L := roots_galois hr hw
  have pi := Nat.prime_iff_prime_int.mp pr
  let I : Ideal ℤ := Ideal.span {(p:ℤ)}
  have : I.IsPrime := (Ideal.span_singleton_prime pi.ne_zero).mpr pi
  apply (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L) pi).mpr
  intro P hP above
  let : P.IsMaximal := hP
  let : P.LiesOver I := above
  have out {a : ℤ} (pn : ¬(p:ℤ)∣a) : (a:𝓞 L)∉P := by
    intro h
    exact pn (Ideal.mem_span_singleton.mp ((Ideal.mem_of_liesOver P I a).mpr h))
  have p2 : ¬(p:ℤ)∣2 := by
    intro h
    apply odd
    exact (Nat.prime_dvd_prime_iff_eq pr Nat.prime_two).mp (by exact_mod_cast h)
  have bot := inertia_trivial hr hw P (by simpa using out p2) (out hd) (out he)
  apply Ideal.ramificationIdx_eq_one_iff.mp
  rw [←Ideal.ramificationIdxIn_eq_ramificationIdx I P (L ≃ₐ[ℚ] L),
    ←Ideal.card_inertia_eq_ramificationIdxIn (G:=L ≃ₐ[ℚ] L) I P,bot]
  simp

end
end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.inertia_root
#print axioms Sun28.FiveDescent.ResidueField.inertia_trivial

#print axioms Sun28.FiveDescent.ResidueField.prime_not_dvd_discr
