import SignedImages

namespace Sun28.ScalarRankZero
open Sun28.FactorHeights

/-- A rational weighted-projective representative of Cremona's quartic, including v=0. -/
def rationalQuartic (A B e:ℤ) : Prop :=
  ∃u v z:ℚ, (u≠0 ∨ v≠0) ∧ z^2=quartic (e:ℚ) (A:ℚ) ((B/e:ℤ):ℚ) u v

private theorem atInfinity {A B e:ℤ} {z:ℚ} (eq:z^2=(e:ℚ)) : represented A B e := by
  have sq:IsSquare (e:ℚ) := ⟨z,by simpa only [sq] using eq.symm⟩
  obtain ⟨Z,hZ⟩:=Rat.isSquare_intCast_iff.mp sq
  refine ⟨1,0,Z,by decide,?_⟩
  simp only [quartic,one_pow,zero_pow (by decide : 4≠0),zero_pow (by decide : 2≠0),
    mul_zero,mul_one,add_zero]
  simpa only [pow_two] using hZ.symm

/-- Primitive integral and rational weighted-projective solubility coincide, including both exceptional coordinates. -/
theorem represented_iff_projective (A B e:ℤ) : represented A B e ↔ rationalQuartic A B e := by
  constructor
  · rintro ⟨u,v,z,cop,eq⟩
    refine ⟨u,v,z,?_,?_⟩
    · by_contra! h
      have u0:u=0:=by exact_mod_cast h.1
      have v0:v=0:=by exact_mod_cast h.2
      simp [u0,v0] at cop
    · simpa [quartic] using congrArg (Int.castRingHom ℚ) eq
  · rintro ⟨u,v,z,guard,eq⟩
    by_cases vn:v=0
    · have un:u≠0:=guard.resolve_right (not_not.mpr vn)
      apply atInfinity (z:=z/u^2)
      rw [vn] at eq
      simp [quartic] at eq
      field_simp
      linear_combination eq
    · let t:=u/v
      have num:(t.num:ℚ)=t*t.den := (div_eq_iff (by exact_mod_cast t.den_nz)).mp t.num_div_den
      have ev : (z/v^2)^2=quartic (e:ℚ) (A:ℚ) ((B/e:ℤ):ℚ) t 1 := by
        dsimp [t,quartic]; field_simp; unfold quartic at eq; linear_combination eq
      have sq':IsSquare ((quartic e A (B/e) t.num (t.den:ℤ):ℤ):ℚ) := by
        refine ⟨(z/v^2)*t.den^2,?_⟩
        push_cast [quartic]
        rw [num]
        unfold quartic at ev
        linear_combination -(t.den:ℚ)^4*ev
      obtain ⟨Z,hZ⟩:=Rat.isSquare_intCast_iff.mp sq'
      refine ⟨t.num,t.den,Z,?_,?_⟩
      · simpa only [Int.natAbs_natCast] using t.reduced
      · simpa only [sq] using hZ.symm

theorem exact_images :
    images 10 24=({1,-1,6,-6}:Finset ℤ) ∧
    images 503 28096=({1,-1,439,-439}:Finset ℤ) ∧
    images (-20) 4=({1}:Finset ℤ) ∧ images (-1006) 140625=({1}:Finset ℤ) := by
  classical
  have member (A B e u v z:ℤ) (he:e∈signedDivisors B)
      (hp:u.natAbs.Coprime v.natAbs) (eq:z^2=quartic e A (B/e) u v) : e∈images A B :=
    Finset.mem_filter.mpr ⟨he,u,v,z,hp,eq⟩
  have d1 : signedDivisors 24={1,-1,2,-2,3,-3,6,-6} := supports.1
  have d2 : signedDivisors 28096={1,-1,2,-2,439,-439,878,-878} := supports.2.2.1
  have t1 : signedDivisors 4={1,-1,2,-2} := supports.2.1
  have t2 : signedDivisors 140625={1,-1,3,-3,5,-5,15,-15} := supports.2.2.2
  refine ⟨Finset.Subset.antisymm direct_images.1 ?_,Finset.Subset.antisymm direct_images.2 ?_,
    Finset.Subset.antisymm dual_images.1 ?_,Finset.Subset.antisymm dual_images.2 ?_⟩
  · intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl|rfl|rfl|rfl
    · exact member _ _ _ 1 0 1 (by rw [d1];decide) (by decide) (by decide)
    · exact member _ _ _ 2 1 0 (by rw [d1];decide) (by decide) (by decide)
    · exact member _ _ _ 0 1 2 (by rw [d1];decide) (by decide) (by decide)
    · exact member _ _ _ 1 1 0 (by rw [d1];decide) (by decide) (by decide)
  · intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl|rfl|rfl|rfl
    · exact member _ _ _ 1 0 1 (by rw [d2];decide) (by decide) (by decide)
    · exact member _ _ _ 8 1 0 (by rw [d2];decide) (by decide) (by decide)
    · exact member _ _ _ 0 1 8 (by rw [d2];decide) (by decide) (by decide)
    · exact member _ _ _ 1 1 0 (by rw [d2];decide) (by decide) (by decide)
  · intro e he
    obtain rfl:=Finset.mem_singleton.mp he
    exact member _ _ _ 1 0 1 (by rw [t1];decide) (by decide) (by decide)
  · intro e he
    obtain rfl:=Finset.mem_singleton.mp he
    exact member _ _ _ 1 0 1 (by rw [t2];decide) (by decide) (by decide)

end Sun28.ScalarRankZero
#print axioms Sun28.ScalarRankZero.represented_iff_projective
#print axioms Sun28.ScalarRankZero.exact_images
