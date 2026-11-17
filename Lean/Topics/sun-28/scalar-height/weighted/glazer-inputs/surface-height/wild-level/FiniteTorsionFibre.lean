import CatalogueLevel28
import InertiaArtin

namespace ZInQBlueprint.WildLevel
open NumberField Finset ZInQKernel.Contrib.HilbertDifferent
open scoped NumberField
noncomputable section

/-- Local data for the original full-torsion route. The first two relative
indices divide 576 and 24. The remaining tame factor can have any size.
The character field and the final quadratic extension add at most two
dyadic orders and no odd wild order. -/
structure TorsionTower (p e : ℕ) where
  levelIndex : ℕ
  torsionIndex : ℕ
  addedIndex : ℕ
  tower : e = levelIndex*torsionIndex*addedIndex
  levelDvd : levelIndex ∣ 576
  torsionDvd : torsionIndex ∣ 24
  twist : addedIndex.factorization p ≤ (if p = 2 then 2 else 0)

theorem torsion_tower_order {e p : ℕ} (hp:p.Prime) (he:0<e) (T : TorsionTower p e) :
    padicValNat p e ≤ if p=2 then 11 else if p=3 then 3 else 0 := by
  have e1 : T.levelIndex*T.torsionIndex≠0 := by intro h;rw [T.tower,h,zero_mul] at he;omega
  have et : T.addedIndex≠0 := by intro h;rw [T.tower,h,mul_zero] at he;omega
  have div := Nat.mul_dvd_mul T.levelDvd T.torsionDvd
  have cap := (Nat.factorization_le_iff_dvd e1 (by decide : 576*24≠0)).mpr div p
  have eqn : 576*24=2^9*3^3 := by decide
  rw [eqn,Nat.factorization_mul (by decide : 2^9≠0) (by decide : 3^3≠0),Nat.factorization_pow,Nat.factorization_pow] at cap
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at cap
  rw [←Nat.factorization_def _ hp,T.tower,Nat.factorization_mul e1 et,Finsupp.add_apply]
  refine (Nat.add_le_add cap T.twist).trans ?_
  by_cases two : p = 2
  · subst p; norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]
  by_cases three : p = 3
  · subst p; norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]
  simp [two,three,Nat.prime_two.factorization,Nat.prime_three.factorization]

/-- An independent bound in the actual prime ideal of a global finite
torsion field. It uses the Hilbert different formula at that prime. -/
theorem full_torsion_conductor (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (p : ℕ) [h : Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p:ℤ)})]
    (T : TorsionTower p (P.ramificationIdx ℤ)) (n t a : ℕ) (c : ℕ → ℕ) (tame:t≤2)
    (dimension : ∀ j,c j≤2) (detects : ∀ j,ramGroup L P (j+1)=⊥ → c j=0)
    (artin : P.ramificationIdx ℤ*a=P.ramificationIdx ℤ*t+∑ j∈range n,ramCard L P (j+1)*c j) :
    a ≤ if p=2 then 46 else if p=3 then 14 else 2 := by
  have x:=torsion_tower_order h.out (Ideal.ramificationIdx_pos ℤ P) T
  have y:=conductor_on_fibre_field L p P n t a c tame dimension detects artin
  split_ifs at x ⊢ <;> omega

/-- The full Artin conductor for an action of the actual inertia group. -/
theorem conductor_of_torsion_action (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (p : ℕ) [h : Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p:ℤ)})]
    (T : TorsionTower p (P.ramificationIdx ℤ)) {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (dim : Module.finrank k V=2)
    (σ : Representation k (Sun28.SurfaceHeight.InertiaArtin.inertia L P) V) :
    Sun28.SurfaceHeight.InertiaArtin.conductor L P p σ ≤ if p=2 then 46 else if p=3 then 14 else 2 := by
  have v:=torsion_tower_order h.out (Ideal.ramificationIdx_pos ℤ P) T
  have a:=Sun28.SurfaceHeight.InertiaArtin.conductor_le L P p σ
  rw [dim] at a
  have q : (padicValNat p (P.ramificationIdx ℤ) : ℚ) ≤ ((if p=2 then 11 else if p=3 then 3 else 0 : ℕ) : ℚ) := by exact_mod_cast v
  refine a.trans ?_
  have b := add_le_add (le_refl (1:ℚ)) (mul_le_mul_of_nonneg_left q (by norm_num : (0:ℚ) ≤ 2))
  apply (mul_le_mul_of_nonneg_left b (by norm_num : (0:ℚ) ≤ 2)).trans
  split_ifs <;> norm_num


end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.torsion_tower_order
#print axioms ZInQBlueprint.WildLevel.full_torsion_conductor

#print axioms ZInQBlueprint.WildLevel.conductor_of_torsion_action
