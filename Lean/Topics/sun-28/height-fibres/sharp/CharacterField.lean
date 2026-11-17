import PellField
/-! Character discriminants on common prime support. -/
namespace Sun28.HeightFibres.Sharp
open Sun28.FiveMarkUnits Polynomial
noncomputable section

/-- The conductor–discriminant formula for an elementary abelian quadratic
extension on common prime support. Each odd prime divides zero or two of
the three quadratic conductors; the three fundamental-discriminant factors
at two are bounded by the product of three factors four. -/
def ConductorDiscriminants : Prop :=
  ∀ (S : Finset ℕ) (g h k : ℤ) (r w : Omega), (∀ p∈S,p.Prime) → g≠0 → h≠0 → k≠0 →
    g.natAbs.primeFactors⊆S → h.natAbs.primeFactors⊆S → k.natAbs.primeFactors⊆S →
    r^2=(g:Omega)*h → w^2=(g:Omega)*k →
    (NumberField.discr (IntermediateField.adjoin ℚ ({r,w} : Set Omega))).natAbs ≤64*(primeProduct S)^2

/-- Lemma 3.5 (3.7) of Bérczes–Evertse–Győry, using class number at least one. -/
def Regulator35 : Prop :=
  ∀ (L : IntermediateField ℚ Omega) [FiniteDimensional ℚ L], Module.finrank ℚ L≤4 →
    let D:ℝ:=(NumberField.discr L).natAbs
    NumberField.Units.regulator L≤Real.sqrt D*(logStar D)^3

open private root_degree from PellField

theorem character_field {S : Finset ℕ} {g h k : ℤ} (ng : g≠0) (nh : h≠0) (nk : k≠0)
    (pr : ∀ p∈S,p.Prime) (gs : g.natAbs.primeFactors⊆S) (hs : h.natAbs.primeFactors⊆S)
    (ks : k.natAbs.primeFactors⊆S) (disc : ConductorDiscriminants) :
    ∃ L : IntermediateField ℚ Omega, ∃ _ : FiniteDimensional ℚ L, Module.finrank ℚ L≤4 ∧
      (∃ r : L,r^2=(g:L)/(h:L)) ∧ (∃ w : L,w^2=(g:L)/(k:L)) ∧
      (NumberField.discr L).natAbs≤64*(primeProduct S)^2 := by
  obtain ⟨r,hr⟩:=IsAlgClosed.exists_pow_nat_eq ((g*h:ℤ):Omega) (by decide : 0<2)
  obtain ⟨w,hw⟩:=IsAlgClosed.exists_pow_nat_eq ((g*k:ℤ):Omega) (by decide : 0<2)
  let L:=IntermediateField.adjoin ℚ ({r,w} : Set Omega)
  let R:=IntermediateField.adjoin ℚ ({r}:Set Omega)
  let W:=IntermediateField.adjoin ℚ ({w}:Set Omega)
  have eq : R ⊔ W=L := by dsimp [L,R,W];rw [←IntermediateField.adjoin_union,Set.singleton_union]
  have dim : Module.finrank ℚ L≤4 := by
    rw [←eq]
    exact (IntermediateField.finrank_sup_le R W).trans (Nat.mul_le_mul (root_degree _ hr) (root_degree _ hw))
  let rL : L:=⟨r,IntermediateField.mem_adjoin_pair_left ℚ r w⟩
  let wL : L:=⟨w,IntermediateField.mem_adjoin_pair_right ℚ r w⟩
  have sr : rL^2=(g:L)*h := Subtype.ext (by simpa using hr)
  have sw : wL^2=(g:L)*k := Subtype.ext (by simpa using hw)
  refine ⟨L,finitePair r w,dim,⟨rL/(h:L),?_⟩,⟨wL/(k:L),?_⟩,?_⟩
  · rw [div_pow,sr]
    field_simp [show (h:L)≠0 by exact_mod_cast nh]
  · rw [div_pow,sw]
    field_simp [show (k:L)≠0 by exact_mod_cast nk]
  · exact disc S g h k r w pr ng nh nk gs hs ks (by simpa using hr) (by simpa using hw)

end
end Sun28.HeightFibres.Sharp
#print axioms Sun28.HeightFibres.Sharp.character_field
