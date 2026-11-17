import LiteralRay
import PrimeIdealNorm

namespace Sun28.Reciprocity
open Sun28.RayDensity Sun28.RayDensity.Artin Submodule.IsPrincipal
noncomputable section
variable {I:Type*} [Fintype I] (q:I→ℕ) [∀i,Fact (q i).Prime]
variable (cop:Pairwise (Function.onFun Nat.Coprime (levels q)))

include cop in
/-- A primary generator for every actual ideal coprime to the modulus, including composite ideals. -/
theorem primary_generator (J:coprimeIdeals (M q)) :
    ∃ z:GaussianInt, principal z=J.val ∧ ((z.re:ZMod 16),(z.im:ZMod 16))∈primarySet ∧
      ∀ i,(z.re:ZMod (q i))^2+(z.im:ZMod (q i))^2≠0 := by
  let x:=generator J.val
  have hx:IsUnit (residue (M q) x) := (invertible_iff _ _).2 (by
    unfold x principal;rw [Ideal.span_singleton_generator];exact J.2)
  let t:=crtUnits q cop hx.unit
  obtain ⟨j,h⟩:=normalized_unit (t none)
  let u:=quarter j
  let z:=x*(u:GaussianInt)
  have hJ : principal z=J.val := by
    change Ideal.span {x*(u:GaussianInt)}=J.val
    rw [←Ideal.span_singleton_mul_span_singleton,Ideal.span_singleton_eq_top.mpr u.isUnit]
    simp [x]
  have val (j:Option I) : (t j : GR (levels q j))=gaussianRed (levels q j) x := by
    change gaussianCRT (levels q) cop hx.unit.val j=_
    rw [hx.unit_spec,gaussianCRT_mk]
  have prod (j:Option I) : (t j * reducedUnit (levels q j) u : GR (levels q j))=gaussianRed (levels q j) z := by
    change (t j:GR (levels q j)) * gaussianRed (levels q j) (u:GaussianInt)=_
    rw [val,←map_mul]
  refine ⟨z,hJ,?_,?_⟩
  · have e : ↑((show GU 16 from t none)*reducedUnit 16 u) = gaussianRed 16 z := prod none
    have he:=congrArg (fun v:GR 16=>(v.re,v.im)) e
    exact he ▸ h
  · intro i
    let w:GU (q i):=(show GU (q i) from t (some i))*reducedUnit (q i) u
    have eq : (w:GR (q i))=gaussianRed (q i) z := prod (some i)
    have hn := (unitNorm (q i) w).ne_zero
    change (w:GR (q i)).norm≠0 at hn
    rw [eq,norm_coordinates] at hn
    exact hn

theorem prime_ideal_data (J:coprimeIdeals (M q)) :
    ∃ (z:GaussianInt) (dy:((z.re:ZMod 16),(z.im:ZMod 16))∈primarySet)
      (odd:∀ i,(z.re:ZMod (q i))^2+(z.im:ZMod (q i))^2≠0),
      principal z=J.val ∧ Nat.card (GaussianInt ⧸ J.val)=z.norm.natAbs ∧
      idealCoordinates q cop (J:idealRay q)=primeTuple q z.re z.im dy odd := by
  obtain ⟨z,hJ,dy,odd⟩:=primary_generator q cop J
  have eq : principalIdeal q z (generator_unit q cop z dy odd)=J :=
    Subtype.ext hJ
  exact ⟨z,dy,odd,hJ,hJ ▸ quotient_card z,eq ▸ idealCoordinates_generator q cop z dy odd⟩

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.primary_generator
#print axioms Sun28.Reciprocity.prime_ideal_data
