import ClassicalCount
import FlagDensity
namespace Sun28.ConeCount
open Finset Filter Topology Sun28.QuadricSieve Sun28.ConeSieve Sun28.ConeFibres
open Sun28.ContactFactors Sun28.WeightedSelection Sun28.SieveTail Sun28.SinglePrime Sun28.MediumSieve
open scoped Classical
noncomputable section

def flagAt {A : Fin 3→ℚ} (i j : ↥(shifts A)) : Classes :=
  fun q=>if h:q.Prime then letI : Fact q.Prime:=⟨h⟩; actualFlag q i j else ∅

def density {A : Fin 3→ℚ} (i j : ↥(shifts A)) (q : ℕ) :=
  factor localWeight q (flagAt i j q)

def classes {A : Fin 3→ℚ} (i j : ↥(shifts A)) (p : ℕ) [Fact p.Prime] : Classes :=
  Function.update (flagAt i j) p (residues p (gap i j))

theorem density_eq {A : Fin 3→ℚ} (i j : ↥(shifts A)) {q : ℕ} [Fact q.Prime] :
    density i j q=fullDensity q i j := by
  simp [density,factor,localWeight,flagAt,fullDensity,(Fact.out : q.Prime)]
  ring

theorem all_classes {A : Fin 3→ℚ} (i j : ↥(shifts A)) (p : ℕ) [Fact p.Prime]
    (q : ℕ) (hp:q.Prime) {x : Point (ZMod q)} (hx:x∈classes i j p q) :
    onCone (gap i j:ZMod q) x ∧ x≠0 := by
  let _ : Fact q.Prime:=⟨hp⟩
  by_cases e : q=p
  · subst q;exact collision_classes (by simpa [classes] using hx)
  · have flag : x∈actualFlag q i j := by simpa [classes,flagAt,e,hp] using hx
    exact ⟨(mem_actualFlag.mp flag).1,(mem_actualFlag.mp flag).2.1⟩

theorem main_factors {A : Fin 3→ℚ} (i j : ↥(shifts A)) (p : ℕ) [Fact p.Prime]
    (u : Finset ℕ) (out : p∉u) :
    main localWeight (insert p u) (classes i j p) =
    factor localWeight p (residues p (gap i j)) * ∏ q∈u,density i j q := by
  rw [main,prod_insert out]
  simp only [classes,Function.update_self]
  congr 1
  apply prod_congr rfl; intro q h
  have ne : q≠p:=fun e=>out (e ▸ h)
  rw [Function.update_of_ne ne]
  rfl

theorem counted_flags {A : Fin 3→ℚ} (j t p : ℕ) [Fact p.Prime] (i k : ↥(shifts A))
    (narrow : 8*(maxCoefficient A+1)≤j+1) (P u : Finset ℕ)
    (pr : ∀ q∈P,q.Prime) (out : p∉P) (sub : u⊆P) :
    let F:=ConeReal.majorant j t p i k narrow
    intersections F.support F.weight (badFactors i P) u =
      count (gap i k) 2 (side t) (ConeReal.weight j) (insert p u) (classes i k p) := by
  classical
  let S:=coneBox (gap i k) 2 (side t)
  let V:=classes i k p
  have accepted (x : Point ℤ) (hx : x∈S) :
      accepts (insert p u) V x ↔ reduction p x∈residues p (gap i k) ∧ u⊆badFactors i P x := by
    have on:= (mem_filter.mp hx).2
    have atq (q : ℕ) (hq:q∈u) : reduction q x∈V q ↔ q∈badFactors i P x := by
      have prime:=pr q (sub hq)
      let _ : Fact q.Prime:=⟨prime⟩
      have diff : q≠p:= fun eq=>out (eq ▸ sub hq)
      simpa [V,classes,flagAt,prime,diff,sub hq] using
        (mem_badFactors_iff i k P x on (p:=q)).symm
    simp only [accepts,forall_mem_insert]
    constructor
    · rintro ⟨h,r⟩;exact ⟨by simpa [V,classes] using h,fun q hq=>(atq q hq).mp (r q hq)⟩
    · rintro ⟨h,r⟩;exact ⟨by simpa [V,classes] using h,fun q hq=>(atq q hq).mpr (r hq)⟩
  have source : ConeReal.sample p (gap i k) (side t)=S.filter (fun x=>reduction p x∈residues p (gap i k)) := by
    ext x;simp only [ConeReal.sample,S,coneBox,mem_filter];tauto
  change (∑ x∈ConeReal.sample p (gap i k) (side t),ConeReal.weight j (normalized (side t) x)*indicator (u⊆badFactors i P x))=_
  simp only [source,indicator,mul_ite,mul_one,mul_zero,←sum_filter]
  apply sum_congr _ (fun _ _=>rfl)
  ext x
  simp only [mem_filter]
  change (x∈S ∧ reduction p x∈residues p (gap i k)) ∧ u⊆badFactors i P x ↔ x∈S ∧ accepts (insert p u) V x
  constructor
  · rintro ⟨⟨s,r⟩,h⟩;exact ⟨s,(accepted x s).mpr ⟨r,h⟩⟩
  · rintro ⟨s,h⟩;exact ⟨⟨s,((accepted x s).mp h).1⟩,((accepted x s).mp h).2⟩

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.density_eq
#print axioms Sun28.ConeCount.main_factors
#print axioms Sun28.ConeCount.counted_flags
