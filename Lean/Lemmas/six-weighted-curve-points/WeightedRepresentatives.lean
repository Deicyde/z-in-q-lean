import WeightedPointSigns

/-! Normal representatives for a binary sextic in the weighted projective plane. -/
namespace ZInQBlueprint.WeightedCurvePoints
open CurveChart
variable {K : Type*} [Field K]
variable (F : K × K → K)

abbrev Finite := {q : K × K // q.2 ^ 2 = F (q.1, 1)}
abbrev Infinity := {y : K // y ^ 2 = F (1, 0)}
abbrev Normal := Finite F ⊕ Infinity F

def finiteRep (q : Finite F) : Rep F :=
  ⟨(q.1.1, 1), q.1.2, by simp, q.2⟩

def infinityRep (q : Infinity F) : Rep F :=
  ⟨(1, 0), q.1, by simp, q.2⟩

def toWeighted : Normal F → Points F
  | .inl q => Quotient.mk _ (finiteRep F q)
  | .inr q => Quotient.mk _ (infinityRep F q)

theorem toWeighted_injective : Function.Injective (toWeighted F) := by
  rintro (p | p) (q | q) h
  · obtain ⟨c,hb,hy⟩ := Quotient.exact h
    have h1 : (c : K) = 1 := by simpa [finiteRep,Units.smul_def] using
      (congrArg Prod.snd hb).symm
    have hx := congrArg Prod.fst hb
    apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext
    · simpa [finiteRep, Units.smul_def,h1] using hx.symm
    · simpa [finiteRep, h1] using hy.symm
  · obtain ⟨c,hb,_⟩ := Quotient.exact h
    have hh := congrArg Prod.snd hb
    simp [finiteRep, infinityRep, Units.smul_def] at hh
    exact (c.ne_zero hh.symm).elim
  · obtain ⟨c,hb,_⟩ := Quotient.exact h
    have hh := congrArg Prod.snd hb
    simp [finiteRep, infinityRep, Units.smul_def] at hh
  · obtain ⟨c,hb,hy⟩ := Quotient.exact h
    have h1 : (c : K) = 1 := by simpa [infinityRep,Units.smul_def] using
      (congrArg Prod.fst hb).symm
    exact congrArg Sum.inr (Subtype.ext (by simpa [infinityRep,h1] using hy.symm))

def scaleRep (hom : ∀ c x z : K, F (c*x,c*z) = c^6 * F (x,z))
    (r : Rep F) (c : Kˣ) : Rep F where
  base := c • r.base
  y := (c : K)^3 * r.y
  nonzero := by
    intro h
    apply r.nonzero
    simpa using congrArg (fun t : K × K => c⁻¹ • t) h
  equation := by
    change ((c : K)^3 * r.y)^2 = F ((c : K)*r.base.1, (c : K)*r.base.2)
    rw [hom, mul_pow, r.equation]
    ring

theorem toWeighted_surjective (hom : ∀ c x z : K, F (c*x,c*z) = c^6 * F (x,z)) :
    Function.Surjective (toWeighted F) := by
  intro p
  induction p using Quotient.inductionOn with
  | _ r =>
    by_cases hn : r.base.2 = 0
    · have hx : r.base.1 ≠ 0 := fun h => r.nonzero (Prod.ext h hn)
      let c := (Units.mk0 r.base.1 hx)⁻¹
      let s := scaleRep F hom r c
      have hb : s.base = (1,0) := by
        apply Prod.ext <;> simp [s,scaleRep,c,Units.smul_def,hx,hn]
      let v : Infinity F := ⟨s.y, hb ▸ s.equation⟩
      refine ⟨.inr v, (Quotient.sound ?_).symm⟩
      exact ⟨c,hb.symm,rfl⟩
    · let c := (Units.mk0 r.base.2 hn)⁻¹
      let s := scaleRep F hom r c
      have hz : s.base.2 = 1 := by simp [s,scaleRep,c,Units.smul_def,hn]
      have hb : s.base = (s.base.1,1) := Prod.ext rfl hz
      let v : Finite F := ⟨(s.base.1,s.y), hb ▸ s.equation⟩
      refine ⟨.inl v, (Quotient.sound ?_).symm⟩
      exact ⟨c,hb.symm,rfl⟩

noncomputable def normalEquiv (hom : ∀ c x z : K, F (c*x,c*z) = c^6 * F (x,z)) :
    Normal F ≃ Points F :=
  Equiv.ofBijective (toWeighted F) ⟨toWeighted_injective F,toWeighted_surjective F hom⟩
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.toWeighted_injective
#print axioms ZInQBlueprint.WeightedCurvePoints.toWeighted_surjective
#print axioms ZInQBlueprint.WeightedCurvePoints.normalEquiv
