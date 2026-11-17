import RadicalDegree
import Mathlib.LinearAlgebra.Dimension.Free

namespace ZInQBlueprint.LevelExtension
noncomputable section
universe u v

private theorem tower {K : Type u} [Field K] [CharZero K] {L : Type v} [Field L] [Algebra K L]
    (D : List K) (ind : IndependentRadicals D) (roots : ∀ d∈D,IsSquare (algebraMap K L d)) :
    ∃ (T : Type u) (_ : Field T) (_ : CharZero T) (_ : Algebra K T),
      Module.finrank K T = 2 ^ D.length ∧ Nonempty (T →ₐ[K] L) ∧
      ∀ b, Avoids D b → ¬IsSquare (algebraMap K T b) := by
  induction D with
  | nil =>
    exact ⟨K,inferInstance,inferInstance,inferInstance,by simp,⟨Algebra.ofId K L⟩,by
      intro b h; simpa [Avoids] using h⟩
  | cons d ds ih =>
    obtain ⟨avoid,ind'⟩:=ind
    obtain ⟨T,field,char0,alg,degree,⟨f⟩,detect⟩:=ih ind' (fun t ht=>roots t (List.mem_cons_of_mem d ht))
    let e := algebraMap K T d
    let : Fact (¬IsSquare e) := ⟨detect d avoid⟩
    let U := QuadraticAlgebra T e 0
    let algL : Algebra T L := f.toRingHom.toAlgebra
    let : IsScalarTower K T L := IsScalarTower.of_algebraMap_eq (R:=K) (S:=T) (A:=L)
      (fun a => (f.commutes a).symm)
    obtain ⟨w,hw⟩:=roots d List.mem_cons_self
    have rel : w*w = e • (1:L)+(0:T) • w := by
      rw [zero_smul,add_zero,Algebra.smul_def,mul_one]
      exact hw.symm.trans (f.commutes d).symm
    let lift : U →ₐ[T] L := QuadraticAlgebra.lift ⟨w,rel⟩
    refine ⟨U,inferInstance,inferInstance,inferInstance,?_,⟨lift.restrictScalars K⟩,?_⟩
    · rw [←Module.finrank_mul_finrank K T U,degree,QuadraticAlgebra.finrank_eq_two]
      simp [pow_succ]
    · intro b pair hs
      have hsq : IsSquare (algebraMap T U (algebraMap K T b)) := by
        rwa [←IsScalarTower.algebraMap_apply]
      obtain ha|hb:=square_over_quadratic (a:=e) hsq
      · exact detect _ pair.1 ha
      · apply detect (b*d) pair.2
        rwa [map_mul]

/-- If a field contains square roots of every entry of an independent squareclass
list, the full Kummer degree divides its degree over the base field. -/
theorem radical_degree_dvd {K : Type u} [Field K] [CharZero K] {L : Type v} [Field L] [Algebra K L]
    (D : List K) (ind : IndependentRadicals D) (roots : ∀ d∈D,IsSquare (algebraMap K L d)) :
    2^D.length ∣ Module.finrank K L := by
  obtain ⟨T,field,char0,alg,deg,⟨f⟩,_⟩:=tower D ind roots
  let algL : Algebra T L := f.toRingHom.toAlgebra
  let : IsScalarTower K T L := IsScalarTower.of_algebraMap_eq (R:=K) (S:=T) (A:=L)
    (fun a => (f.commutes a).symm)
  rw [←deg]
  exact Module.finrank_dvd_finrank_right K T L

end
end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.radical_degree_dvd
