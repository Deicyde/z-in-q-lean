import ConjugationGroup

namespace Sun28.RayDensity
open SemidirectProduct
noncomputable section
variable {I : Type*} (q : I→ℕ) [∀ i,Fact (q i).Prime]

def conjAut (p : ℕ) : MulAut (GU p) where
  toFun := conjugate p
  invFun := conjugate p
  map_mul' := map_mul _
  left_inv := fun z=> by
    apply Units.ext
    change star (star (z:GR p))=_
    exact star_star _
  right_inv := fun z=> by
    apply Units.ext
    change star (star (z:GR p))=_
    exact star_star _

variable {A : Type*} [CommGroup A]

def joinedAut (s : MulAut A) : MulAut (A × ((i:I)→GU (q i))) where
  toFun z := (s z.1,fun i=>conjAut (q i) (z.2 i))
  invFun z := (s.symm z.1,fun i=>(conjAut (q i)).symm (z.2 i))
  left_inv z := by simp
  right_inv z := by simp
  map_mul' a b := by ext <;> simp

theorem joined_involution (s : MulAut A) (h : s*s=1) : joinedAut q s * joinedAut q s=1 := by
  apply MulEquiv.ext
  intro z
  apply Prod.ext
  · exact DFunLike.congr_fun h z.1
  · apply funext
    intro i
    apply Units.ext
    change star (star (z.2 i:GR (q i)))=(z.2 i:GR (q i))
    exact star_star _

/-- Exact image in primary CRT coordinates. The base class may be any commutative group
with a conjugation automorphism; the new components are the literal Gaussian residue groups. -/
theorem joined_range (s : MulAut A) (odd : ∀ i,q i≠2) :
    (delta (joinedAut q s)).range=(delta s).range.prod
      (Subgroup.pi Set.univ (fun i=>(unitNorm (q i)).ker)) := by
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    constructor
    · exact ⟨v.1,rfl⟩
    · intro i _
      change coboundary (q i) (v.2 i) ∈ (unitNorm (q i)).ker
      rw [←range_coboundary (odd i)]
      exact ⟨v.2 i,rfl⟩
  · rintro ⟨⟨v,h⟩,en⟩
    have each (i:I) : z.2 i∈(coboundary (q i)).range := by
      rw [range_coboundary (odd i)]
      exact en i (Set.mem_univ _)
    choose w hw using each
    exact ⟨(v,w),Prod.ext h (funext hw)⟩

/-- No surjectivity, kernel description or complex-conjugation compatibility is hypothesized
for the extension in this explicit split presentation. -/
theorem full_ray_derived (s : MulAut A) (h : s*s=1) (odd : ∀ i,q i≠2) :
    commutator (SemidirectProduct (A×((i:I)→GU (q i))) C₂
      (act (joinedAut q s) (joined_involution q s h))) =
    ((delta s).range.prod (Subgroup.pi Set.univ (fun i=>(unitNorm (q i)).ker))).map
      (SemidirectProduct.inl (φ:=act (joinedAut q s) (joined_involution q s h))) := by
  rw [semidirect_derived,joined_range q s odd]

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.joined_involution
#print axioms Sun28.RayDensity.joined_range
#print axioms Sun28.RayDensity.full_ray_derived
