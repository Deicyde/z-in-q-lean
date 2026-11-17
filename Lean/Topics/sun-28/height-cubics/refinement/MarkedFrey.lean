import PairBudget

/-! An integral model whose j-invariant is a degree-one function of the marked slope. -/
namespace Sun28.HeightCubics.Refinement
noncomputable section

def frey (d e u v : ℤ) : WeierstrassCurve ℤ :=
  ⟨0, 0, 0, 3*d*e*v, 2*d^2*e*u⟩

def jRatio (E : WeierstrassCurve ℤ) : ℚ := (E.c₄:ℚ)^3/(E.Δ:ℚ)

theorem frey_c4 (d e u v : ℤ) : (frey d e u v).c₄ = -144*d*e*v := by
  simp only [frey, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem frey_discriminant (d e u v : ℤ) :
    (frey d e u v).Δ = -1728*d^3*e^2*(d*u^2+e*v^3) := by
  simp only [frey, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem frey_j {d e u v P Q R : ℤ} (p:P=d*u^2) (q:Q=e*v^3) (sum:P+Q=R)
    (dn:d≠0) (en:e≠0) (rn:R≠0) : jRatio (frey d e u v)=1728*(Q:ℚ)/(R:ℚ) := by
  have den : d*u^2+e*v^3=R := by rw [←p,←q,sum]
  unfold jRatio
  rw [frey_c4,frey_discriminant,den,q]
  push_cast
  field_simp [show (d:ℚ)≠0 by exact_mod_cast dn,show (e:ℚ)≠0 by exact_mod_cast en,
    show (R:ℚ)≠0 by exact_mod_cast rn]
  ring

/-- This fraction is the j-invariant of the generic fibre whenever the discriminant is nonzero. -/
theorem generic_j (W:WeierstrassCurve ℤ) (hn:W.Δ≠0) :
    let E:=W.map (Int.castRingHom ℚ)
    ∃ he:E.IsElliptic, @WeierstrassCurve.j ℚ _ E he=jRatio W := by
  let E:=W.map (Int.castRingHom ℚ)
  have en:E.Δ≠0:=by
    dsimp [E]; rw [WeierstrassCurve.map_Δ]; change (W.Δ:ℚ)≠0; exact_mod_cast hn
  have he:E.IsElliptic:=⟨isUnit_iff_ne_zero.mpr en⟩
  refine ⟨he,?_⟩
  change E.j=jRatio W
  rw [WeierstrassCurve.j,Units.val_inv_eq_inv_val,WeierstrassCurve.coe_Δ',inv_mul_eq_div]
  simp [E,jRatio]

end
end Sun28.HeightCubics.Refinement
#print axioms Sun28.HeightCubics.Refinement.frey_c4
#print axioms Sun28.HeightCubics.Refinement.frey_discriminant
#print axioms Sun28.HeightCubics.Refinement.frey_j
#print axioms Sun28.HeightCubics.Refinement.generic_j
