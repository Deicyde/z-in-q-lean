import SixCanonicalPeriods

/-! Multiplying the raw period equation by the transcendental modular
weight scales its ordinate over ℂ. The resulting dense affine chart
specifies the unique isomorphism of the smooth proper completions. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.ShimuraAtlas
open BinaryCover QuaternionLift NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def rawPolynomial (A B D : ℂ) : ℂ[X] :=
  modularBinary (C A) (C B) (C D) X 1

theorem raw_polynomial_equation (ι : Qbar →+* ℂ) {A Y Z : ℂ} {p : ConicPoint}
    (above : LiesAbove ι A Y Z p) (e l : Qbar) :
    rawPolynomial A (ι e*Y) (2*ι l*Z) =
      C A * (modularPolynomial (e*p.y/3) (l*p.z)).map ι := by
  apply Polynomial.funext
  intro x
  have formula := raw_equation ι above e l x 1
  simpa [rawPolynomial,modularPolynomial,modularBinary,eval_mul,eval_add,eval_sub,eval_pow,
    map_mul,map_add,map_sub,map_pow,map_ofNat] using formula

theorem raw_models {u : ℚ} (hu : u ∉ ZInQ.contactSet) {p : ConicPoint}
    (hp : FibrePoint u p) {e l : Qbar} (he : e^2=-6) (hl : l^2=2) (ι : Qbar →+* ℂ)
    {A Y Z : ℂ} (above : LiesAbove ι A Y Z p) :
    let n := (modularPolynomial (e*p.y/3) (l*p.z)).map ι
    let raw := rawPolynomial A (ι e*Y) (2*ι l*Z)
    ∃ (hN : n.natDegree = 6) (hR : raw.natDegree = 6),
      n.Separable ∧ raw.Separable ∧
      ∃ (a : SpecOver (R := ℂ) (Cover n) ≅ SpecOver (R := ℂ) (Cover raw)),
        ∃! f : sexticCompletion n hN ≅ sexticCompletion raw hR,
          chartInclusion ℂ _ _ (reverse_sextic_overlap hN) false ≫ f.hom =
            a.hom ≫ chartInclusion ℂ _ _ (reverse_sextic_overlap hR) false := by
  dsimp only
  let n := (modularPolynomial (e*p.y/3) (l*p.z)).map ι
  let raw := rawPolynomial A (ι e*Y) (2*ι l*Z)
  have hnA := above.1
  have eq : raw = C A*n := raw_polynomial_equation ι above e l
  have reg := modular_regular hu (rad_spec hu hp he hl).1 (rad_spec hu hp he hl).2.1
    (rad_spec hu hp he hl).2.2.1 (rad_spec hu hp he hl).2.2.2
  have hN : n.natDegree = 6 := by dsimp only [n]; rw [natDegree_map]; exact reg.1
  have hR : raw.natDegree = 6 := by rw [eq,natDegree_C_mul hnA,hN]
  have sn : n.Separable := reg.2.map
  have sr : raw.Separable := by
    rw [eq]
    exact (associated_unit_mul_left _ (C A) (isUnit_C.mpr hnA.isUnit)).symm.separable sn
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq A (by decide : 0<2)
  have hn : v≠0 := fun hv0 => hnA (by rw [←hv,hv0,zero_pow (by decide : 2≠0)])
  let v' := Units.map (C : ℂ →+* ℂ[X]).toMonoidHom (Units.mk0 v hn)
  let a : SpecOver (R := ℂ) (Cover n) ≅ SpecOver (R := ℂ) (Cover raw) :=
    specIso (squareEquiv (AlgEquiv.refl : ℂ[X] ≃ₐ[ℂ] ℂ[X]) v' (by
      change raw = C v ^2*n
      rw [←map_pow,hv,eq]))
  let Xn := sexticCompletion n hN
  let Xr := sexticCompletion raw hR
  obtain ⟨inN,prN,_,_,vN⟩ := sexticCompletion_geometry hN sn
  obtain ⟨inR,prR,_,_,vR⟩ := sexticCompletion_geometry hR sr
  let : AlgebraicGeometry.IsIntegral Xn.left := inN
  let : IsProper Xn.hom := prN
  let : AlgebraicGeometry.IsIntegral Xr.left := inR
  let : IsProper Xr.hom := prR
  let U := SpecOver (R := ℂ) (Cover n)
  let : Nonempty U.left := inferInstanceAs (Nonempty (PrimeSpectrum (Cover n)))
  let i : U ⟶ Xn := chartInclusion ℂ _ _ (reverse_sextic_overlap hN) false
  let j' := chartInclusion ℂ _ _ (reverse_sextic_overlap hR) false
  let j : U ⟶ Xr := a.hom ≫ j'
  let : IsOpenImmersion i.left := chartInclusion_open ..
  let : IsIso a.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso a).hom))
  let oj : IsOpenImmersion j.left := @IsOpenImmersion.comp _ _ _ _ _
    (IsOpenImmersion.of_isIso a.hom.left) (chartInclusion_open ..)
  exact ⟨hN,hR,sn,sr,a,CurveExtension.unique_model_iso (U:=U) i j vN vR⟩

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.raw_polynomial_equation
#print axioms ZInQBlueprint.ShimuraAtlas.raw_models
