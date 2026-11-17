import LocalRatioResidual

namespace Sun28.PointLifts
open Sun28.PointFibres
noncomputable section
set_option maxRecDepth 8192

/-- The square of a rational number with a finite residue determines its reduced denominator and its residue. -/
theorem reduced_square_residue {p : ℕ} [hp : Fact p.Prime] {s : ℚ} {r : ZMod p}
    (H : Residue p (s^2) r) : (s.den:ZMod p)≠0 ∧ ((s.num:ZMod p)/s.den)^2=r := by
  obtain ⟨a,d,dn,eq,re⟩:=H
  have dk : d≠0:=by rintro rfl;simp at dn
  have dp : (d:ℚ)≠0:=by exact_mod_cast dk
  have yn : (s.den:ℚ)≠0:=by exact_mod_cast s.den_nz
  have S:=Rat.num_div_den s
  rw [←S] at eq
  have Q : (s.num:ℚ)^2*d=(a:ℚ)*s.den^2:=by field_simp at eq;linear_combination eq
  have ZZ : s.num^2*d=a*(s.den:ℤ)^2:=by exact_mod_cast Q
  have F : (s.num:ZMod p)^2*d=(a:ZMod p)*(s.den:ZMod p)^2:=by
    simpa using congrArg (Int.castRingHom (ZMod p)) ZZ
  have prim : (s.num:ZMod p)≠0 ∨ (s.den:ZMod p)≠0:=by
    simpa using (primitive_mod (p:=p) (x:=s.num) (y:=(s.den:ℤ)) (by simpa using s.reduced))
  have nz : (s.den:ZMod p)≠0:=by
    intro no
    have xn:=prim.resolve_right (not_not_intro no)
    exact (mul_ne_zero (pow_ne_zero 2 xn) dn) (by simpa [no] using F)
  refine ⟨nz,?_⟩
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero _ nz)).mpr
  apply mul_right_cancel₀ dn
  rw [re] at F
  linear_combination F

private theorem values {p θ : ℕ} [Fact p.Prime] {s : ℚ} (p3 : (3:ZMod p)≠0) (R : RamifiedRay p θ s) :
    let x := (s.num:ZMod p)/s.den
    (s.den:ZMod p)≠0 ∧ (x^2=(θ:ZMod p) ∨ x^2=(-3:ZMod p)*θ ∨ x^2*3= -(θ:ZMod p)) := by
  rcases R with h|h|h <;> obtain ⟨n,e⟩:=reduced_square_residue h
  · exact ⟨n,Or.inl e⟩
  · exact ⟨n,Or.inr (Or.inl e)⟩
  · exact ⟨n,Or.inr (Or.inr ((eq_div_iff p3).mp e))⟩

private instance : Fact (Nat.Prime 11):=⟨by norm_num⟩
private instance : Fact (Nat.Prime 109):=⟨by norm_num⟩
private instance : Fact (Nat.Prime 439):=⟨by norm_num⟩

/-- The exact three finite ray tests for Sun's independently prepared pair. -/
theorem fixed_ramified_residues {s : ℚ} (sn : s≠0) (H : SingleFibre 526361 526681 s) :
    ((s.den:ZMod 11)≠0 ∧ (s.num:ZMod 11)/s.den ∈ ([1,10] : List (ZMod 11))) ∧
    ((s.den:ZMod 109)≠0 ∧ (s.num:ZMod 109)/s.den ∈ ([27,28,50,59,81,82] : List (ZMod 109))) ∧
    ((s.den:ZMod 439)≠0 ∧ (s.num:ZMod 439)/s.den ∈ ([25,75,205,234,364,414] : List (ZMod 439))) := by
  have a:=allowed_of_fibre fixed_conditions.1 sn H
  have L:=a.2.2
  obtain ⟨d1,h1⟩:=values (p:=11) (show (3:ZMod 11)≠0 by decide) (L 11 (by norm_num) (by decide) (show (3:ZMod 11)≠0 by decide))
  obtain ⟨d2,h2⟩:=values (p:=109) (show (3:ZMod 109)≠0 by decide) (L 109 (by norm_num) (by decide) (show (3:ZMod 109)≠0 by decide))
  obtain ⟨d3,h3⟩:=values (p:=439) (show (3:ZMod 439)≠0 by decide) (L 439 (by norm_num) (by decide) (show (3:ZMod 439)≠0 by decide))
  refine ⟨⟨d1,?_⟩,⟨d2,?_⟩,⟨d3,?_⟩⟩
  · exact (show ∀ x : ZMod 11, (x^2=526681 ∨ x^2=(-3:ZMod 11)*526681 ∨ x^2*3= -526681) →
      x∈([1,10] : List (ZMod 11)) by decide) _ h1
  · exact (show ∀ x : ZMod 109, (x^2=526681 ∨ x^2=(-3:ZMod 109)*526681 ∨ x^2*3= -526681) →
      x∈([27,28,50,59,81,82] : List (ZMod 109)) by decide) _ h2
  · exact (show ∀ x : ZMod 439, (x^2=526681 ∨ x^2=(-3:ZMod 439)*526681 ∨ x^2*3= -526681) →
      x∈([25,75,205,234,364,414] : List (ZMod 439)) by decide) _ h3

theorem fixed_ratio_one_empty : ¬SingleFibre 526361 526681 1 := by
  intro h
  have e:=(fixed_ramified_residues one_ne_zero h).2.1.2
  have wrong : (1:ZMod 109)∈([27,28,50,59,81,82] : List (ZMod 109)):=by simpa using e
  exact (by decide : ¬(1:ZMod 109)∈([27,28,50,59,81,82] : List (ZMod 109))) wrong

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.reduced_square_residue
#print axioms Sun28.PointLifts.fixed_ramified_residues
#print axioms Sun28.PointLifts.fixed_ratio_one_empty
