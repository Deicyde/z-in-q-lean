import QuarticEquivalence
import DiagonalCover

namespace ZInQBlueprint.BranchId
open Diagonal210
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

private theorem alg_rat (u : ℚ) : algebraMap ℚ K u=(u:K) := by
  simp

def restrictRow (i : Fin 4) (y : Fin 4 → K) (j : Fin 3) : K := y (keep i j)

theorem omitted_of_fibre {s : ℚ} (y : Fibre K coefficient s) (i : Fin 4) :
    omitted i (s:K) (restrictRow i y.1) := by
  intro j
  simpa only [restrictRow, map_mul, map_sub, alg_rat] using y.2 (keep i j)

/-- The two rows have exactly the columns 2 and 3 in common. -/
theorem glue_rows {s : ℚ} {z w : Fin 3 → K} (hz : omitted 0 (s:K) z)
    (hw : omitted 1 (s:K) w) :
    (∃! y : Fibre K coefficient s, restrictRow 0 y.1=z ∧ restrictRow 1 y.1=w) ↔
    z 1=w 1 ∧ z 2=w 2 := by
  constructor
  · rintro ⟨y,⟨hy,hw'⟩,_⟩
    rw [←hy,←hw']
    exact ⟨rfl,rfl⟩
  · rintro ⟨e1,e2⟩
    let a : Fin 4 → K := ![w 0,z 0,z 1,z 2]
    have ha : ∀i,(a i)^2=algebraMap ℚ K (coefficient i*(s-mark i)) := by
      intro i
      simp only [map_mul,map_sub,alg_rat]
      fin_cases i
      · exact hw 0
      · exact hz 0
      · exact hz 1
      · exact hz 2
    let y : Fibre K coefficient s := ⟨a,ha⟩
    refine ⟨y,⟨?_,?_⟩,?_⟩
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j
      · rfl
      · exact e1
      · exact e2
    · rintro v ⟨h0,h1⟩
      apply Subtype.ext
      funext i
      fin_cases i
      · exact congrFun h1 0
      · exact congrFun h0 0
      · exact congrFun h0 1
      · exact congrFun h0 2

/-- Two points on the actual 105 and 70 quartics above the same rational slope
have a unique common lift precisely when their two shared signed coordinates agree. -/
theorem published_pair_lift {s : ℚ} (p : PublishedOpen 0 K) (q : PublishedOpen 1 K)
    (hp : ((quarticEquiv 0) p).1.1=(s:K)) (hq : ((quarticEquiv 1) q).1.1=(s:K)) :
    (∃! y : Fibre K coefficient s, restrictRow 0 y.1=((quarticEquiv 0) p).1.2 ∧
       restrictRow 1 y.1=((quarticEquiv 1) q).1.2) ↔
    ((quarticEquiv 0) p).1.2 1=((quarticEquiv 1) q).1.2 1 ∧
    ((quarticEquiv 0) p).1.2 2=((quarticEquiv 1) q).1.2 2 :=
  glue_rows (hp ▸ ((quarticEquiv 0) p).2.1) (hq ▸ ((quarticEquiv 1) q).2.1)

end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.omitted_of_fibre
#print axioms ZInQBlueprint.BranchId.glue_rows
#print axioms ZInQBlueprint.BranchId.published_pair_lift
