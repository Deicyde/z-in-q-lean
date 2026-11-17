import IntegralCounts
namespace Sun28.ConeCount
open Finset Sun28.QuadricSieve Sun28.ConeSieve
open scoped Classical
noncomputable section

def entire (κ : ℤ) (R B : ℕ) (ψ : Point ℝ→ℝ) :=
  ∑ x∈coneBox κ R B,ψ (normalized B x)

def single (q : ℕ) (V : Finset (Point (ZMod q))) : Classes :=
  Function.update (fun _=>∅) q V

private theorem dilate_inj {q : ℕ} (pos : 0<q) : Function.Injective (dilate q) := by
  intro x y h
  have n : q≠0:=pos.ne'
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩,e⟩
  rcases y with ⟨⟨A,B⟩,⟨C,D⟩,E⟩
  simpa [dilate,n,Prod.ext_iff] using h

private theorem admissible_single {κ : ℤ} {q : ℕ} [NeZero q] {x : Point ℤ}
    (h : onCone κ x) :
    accepts {q} (single q (primitive κ q)) x ↔ reduction q x≠0 := by
  simp [accepts,single,primitive,reduce_cone q h]

theorem primitive_diff (κ : ℤ) (R B q : ℕ) [NeZero q] (ψ : Point ℝ→ℝ) :
    count κ R (q*B) ψ {q} (single q (primitive κ q)) =
      entire κ R (q*B) ψ - entire κ R B ψ := by
  let S:=coneBox κ R (q*B)
  have pred (x) (hx:x∈S) := admissible_single (q:=q) (mem_filter.mp hx).2
  have split : S.filter (accepts {q} (single q (primitive κ q))) = S.filter (fun x=>reduction q x≠0) := by
    apply filter_congr;intro x hx;exact pred x hx
  have pos := Nat.pos_of_ne_zero (NeZero.ne q)
  have image : S.filter (fun x=>reduction q x=0)=(coneBox κ R B).image (dilate q) := by
    ext x
    constructor
    · intro hx
      obtain ⟨h,z⟩:=mem_filter.mp hx
      obtain ⟨y,rfl⟩:=(reduction_zero x).mp z
      exact mem_image.mpr ⟨y,(in_dilated_box pos R B y).mp h,rfl⟩
    · intro hx
      obtain ⟨y,hy,rfl⟩:=mem_image.mp hx
      exact mem_filter.mpr ⟨(in_dilated_box pos R B y).mpr hy,(reduction_zero _).mpr ⟨y,rfl⟩⟩
  have eq : (∑ x∈S.filter (fun x=>reduction q x=0),ψ (normalized (q*B) x))=entire κ R B ψ := by
    rw [image,sum_image (dilate_inj pos).injOn]
    unfold entire
    apply sum_congr rfl;intro x _;rw [scaled_dilate pos]
  have partition:=sum_filter_add_sum_filter_not S (fun x=>reduction q x=0) (fun x=>ψ (normalized (q*B) x))
  unfold count; dsimp only [S] at split
  rw [split];change _= (∑ x∈S,ψ (normalized (q*B) x)) - _
  linarith only [eq,partition]

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.primitive_diff
