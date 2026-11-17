import ResidualFactors
import HenselTriples

/-! Six roots of the actual sextic in its two singular charts. -/
namespace ZInQBlueprint.ClusterRoots
open Polynomial IsLocalRing ZInQBlueprint.ClusterCharts ZInQBlueprint.DiscEquations
open ZInQBlueprint.SexticCalibration ZInQBlueprint.ResidualFactors ZInQBlueprint.HenselTriples
noncomputable section

private theorem enumerate {k : Type*} [Field k] {f : k[X]} {n : ℕ}
    (hs : f.Splits) (hsep : f.Separable) (hn : f.natDegree = n) :
    ∃ x : Fin n → k, Function.Injective x ∧
      ∀ i, f.eval (x i) = 0 ∧ f.derivative.eval (x i) ≠ 0 := by
  classical
  let t := f.roots.toFinset
  have ht : Fintype.card t = n := by
    rw [Fintype.card_coe,Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      ← hs.natDegree_eq_card_roots,hn]
  let v : Fin n ≃ t := (Fintype.equivFinOfCardEq ht).symm
  refine ⟨fun j => (v j).val, Subtype.val_injective.comp v.injective, ?_⟩
  intro i
  have h := isRoot_of_mem_roots (Multiset.mem_toFinset.mp (v i).property)
  exact ⟨h, hsep.eval₂_derivative_ne_zero (RingHom.id _) h⟩

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]

structure SexticFibre (f : R[X]) (c : R) where
  centres : Fin 2 → R
  residues : Fin 2 → Fin 3 → ResidueField R
  triples : TwoTriples f centres c residues
  nonzero : f ≠ 0
  degree : f.natDegree ≤ 6

omit [HenselianRing R (maximalIdeal R)] in
theorem root_iff {f : R[X]} {c : R} (T : SexticFibre f c)
    {K : Type*} [CommRing K] [IsDomain K] (ι : R →+* K) (hi : Function.Injective ι) (z : K) :
    (f.map ι).IsRoot z ↔ ∃ i j, z = ι (T.centres i+c*T.triples.y i j) :=
  rootsInExtension T.triples T.nonzero T.degree ι hi z

private theorem liftRows {f : R[X]} {c : R} {a : Fin 2 → R}
    (hc : c ≠ 0) (hc0 : residue R c = 0) (ha : Function.Injective (fun i => residue R (a i)))
    (hf : f ≠ 0) (hdeg : f.natDegree ≤ 6)
    (P : Fin 2 → (ResidueField R)[X])
    (chart : ∀ i, ∃ g : R[X], (∀ y, f.eval (a i+c*y)=c^3*g.eval y) ∧ g.map (residue R) = P i)
    (hs : ∀ i, (P i).Splits) (hsep : ∀ i, (P i).Separable) (hd : ∀ i, (P i).natDegree=3) :
    Nonempty (SexticFibre f c) := by
  choose g he hm using chart
  choose x hx hroot using fun i => enumerate (hs i) (hsep i) (hd i)
  have hz (i j) : (g i).eval₂ (residue R) (x i j) = 0 := by
    rw [← eval_map,hm]; exact (hroot i j).1
  have hs' (i j) : (g i).derivative.eval₂ (residue R) (x i j) ≠ 0 := by
    rw [← eval_map,← derivative_map,hm]; exact (hroot i j).2
  obtain ⟨T⟩ := twoTriples f a c g x hc hc0 ha he hx hz hs'
  exact ⟨⟨a,x,T,hf,hdeg⟩⟩

private theorem linearSplits {k : Type*} [Field k] (x : k) : (X-C x).Splits := by
  simp

private theorem zeroDegree {k : Type*} [Field k] {a U : k} (h : -4*(2*a+16)^3 ≠ 0) :
    (zeroResidual a U).natDegree=3 := by
  let B := U*slope₀ a
  let A := -4*(2*a+16)^3
  change (C A*X^3 + C B*X).natDegree=3
  have hn : A ≠ 0 := h
  compute_degree!

private theorem poleDegree {k : Type*} [Field k] {a U : k} (h729 : (729:k) ≠ 0)
    (h : 3*(2*a+2)^3 ≠ 0) : (poleResidual a U).natDegree=3 := by
  let A := 3*(2*a+2)^3
  let B := U*firstPole a
  change (C (729:k)*(C A*X^3 + C B)).natDegree=3
  rw [natDegree_C_mul h729]
  have hn : A ≠ 0 := h
  compute_degree!

private theorem four {k : Type*} [Field k] [NeZero (2:k)] : (4:k) ≠ 0 := by
  convert pow_ne_zero 2 (NeZero.ne (2:k)) using 1; norm_num

private theorem nineCube {k : Type*} [Field k] [NeZero (3:k)] : (729:k) ≠ 0 := by
  convert pow_ne_zero 6 (NeZero.ne (3:k)) using 1; norm_num

private theorem pair_inj {k : Type*} {x y : k} (h : x ≠ y) :
    Function.Injective ![x,y] := by
  intro i j e
  fin_cases i <;> fin_cases j <;> simp_all

variable [NeZero (2:ResidueField R)] [NeZero (3:ResidueField R)]

omit [IsDomain R] [HenselianRing R (maximalIdeal R)] [NeZero (3:ResidueField R)] in
private theorem zero_nonzero {c U : R} (hc : residue R c=0) : sextic (c^2*U) ≠ 0 := by
  intro h
  have H := congrArg (fun f : R[X] => residue R (f.coeff 6)) h
  have : -(4:ResidueField R)=0 := by simpa [zero_lead,hc,map_ofNat] using H
  exact (neg_ne_zero.mpr four) this

omit [IsDomain R] [HenselianRing R (maximalIdeal R)] [NeZero (2:ResidueField R)] in
private theorem pole_nonzero {c U : R} (hc : residue R c=0) : polePolynomial (c^3*U) ≠ 0 := by
  intro h
  have H := congrArg (fun f : R[X] => residue R (f.coeff 6)) h
  have : (729:ResidueField R)*3=0 := by simpa [pole_lead,hc,map_ofNat] using H
  exact (mul_ne_zero nineCube (NeZero.ne (3:ResidueField R))) this

/-- The six roots at positive even contact, from square roots of two residue scalars. -/
theorem zero_fibre {c U d : R} (hd : d^2=6) (hc : c ≠ 0) (hc0 : residue R c=0)
    {u v z : ResidueField R} (hu : residue R U = residue R d*u) (hU : residue R U ≠ 0)
    (hv : v^2= -48*u) (hz : z^2=48*u) :
    Nonempty (SexticFibre (sextic (c^2*U)) c) := by
  let a : Fin 2 → R := ![-8+4*d,-8-4*d]
  let ρ := residue R
  have hd' : (ρ d)^2=6 := by simpa [ρ,map_ofNat] using congrArg ρ hd
  have h₆ : (6:ResidueField R) ≠ 0 := by
    convert mul_ne_zero (NeZero.ne (2:ResidueField R)) (NeZero.ne (3:ResidueField R)) using 1; norm_num
  have hd0 : ρ d ≠ 0 := fun e => h₆ (by simpa [e] using hd'.symm)
  have hn : -8+4*ρ d ≠ -8-4*ρ d := by
    intro eq
    apply mul_ne_zero (mul_ne_zero (NeZero.ne (2:ResidueField R)) four) hd0
    linear_combination eq
  have hi : Function.Injective (fun i => ρ (a i)) := by
    convert pair_inj hn using 1
    ext i
    fin_cases i <;> simp [a,map_ofNat]
  have ha (i) : q₀ (a i) = 0 := by
    fin_cases i
    · exact (zero_centres hd).1
    · exact (zero_centres hd).2
  have ha' (i) : q₀ (ρ (a i)) = 0 := by simpa [q₀,map_ofNat] using congrArg ρ (ha i)
  apply liftRows (a:=a) hc hc0 hi (zero_nonzero hc0) (zero_degree _)
    (fun i => zeroResidual (ρ (a i)) (ρ U)) (fun i => zero_chart_reduction ρ (ha i) hc0 U)
  · intro i
    have ff := zero_factors hd' hv hz
    have fm (A w : ResidueField R) :
        (C A*X*(X-C w)*(X+C w)).Splits :=
      (((Splits.C A).mul Splits.X).mul (linearSplits w)).mul (Splits.X_add_C w)
    fin_cases i
    · change (zeroResidual (ρ (-8+4*d)) (ρ U)).Splits
      simp only [map_add,map_neg,map_ofNat,map_mul]
      rw [show ρ U = ρ d*u from hu,ff.1]
      exact fm _ _
    · change (zeroResidual (ρ (-8-4*d)) (ρ U)).Splits
      simp only [map_sub,map_neg,map_ofNat,map_mul]
      rw [show ρ U = ρ d*u from hu,ff.2]
      exact fm _ _
  · intro i
    exact zero_cubic (mul_ne_zero hU (zero_units (ha' i)).2)
  · intro i
    exact zeroDegree (mul_ne_zero (neg_ne_zero.mpr four) (pow_ne_zero _ (zero_units (ha' i)).1))

variable [NeZero (5:ResidueField R)] [NeZero (7:ResidueField R)]

/-- At a pole, the congruence for F modulo G supplies the cube root and G supplies
the roots of unity. The only additional centre coordinate is a square root of two. -/
theorem pole_fibre {c U s : R} (hs : s^2=2) (hc : c ≠ 0) (hc0 : residue R c=0)
    {A B d D : ResidueField R} (hd : d^2=6) (hG : poleForm A B=0)
    (hB : B ≠ 0) (hF : contactProduct A B ≠ 0)
    (hu : 240*d*contactProduct A B*residue R U = D^3) (hU : residue R U ≠ 0) :
    Nonempty (SexticFibre (polePolynomial (c^3*U)) c) := by
  let a : Fin 2 → R := ![-1+s,-1-s]
  let ρ := residue R
  obtain ⟨v,hv⟩ := pole_cube hG hF hd hu
  obtain ⟨z,hz⟩ := pole_unity hG hB
  have hs' : (ρ s)^2=2 := by simpa [ρ,map_ofNat] using congrArg ρ hs
  have hs0 : ρ s ≠ 0 := fun e => (NeZero.ne (2:ResidueField R)) (by simpa [e] using hs'.symm)
  have hn : -1+ρ s ≠ -1-ρ s := by
    intro eq
    apply mul_ne_zero (NeZero.ne (2:ResidueField R)) hs0
    linear_combination eq
  have hi : Function.Injective (fun i => ρ (a i)) := by
    convert pair_inj hn using 1
    ext i
    fin_cases i <;> simp [a]
  have ha (i) : qPole (a i) = 0 := by
    fin_cases i
    · exact (pole_centres hs).1
    · exact (pole_centres hs).2
  have ha' (i) : qPole (ρ (a i)) = 0 := by simpa [qPole,map_ofNat] using congrArg ρ (ha i)
  apply liftRows (a:=a) hc hc0 hi (pole_nonzero hc0) (pole_degree _)
    (fun i => poleResidual (ρ (a i)) (ρ U)) (fun i => pole_chart_reduction ρ (ha i) hc0 U)
  · intro i
    rw [pole_factor (ha' i) hv hz]
    exact (Splits.C _).mul (((linearSplits _).mul (linearSplits _)).mul (linearSplits _))
  · intro i
    apply Separable.unit_mul ((isUnit_iff_ne_zero.mpr nineCube).map C)
    exact pole_cubic (mul_ne_zero hU (pole_units (ha' i)).2)
  · intro i
    exact poleDegree nineCube (mul_ne_zero (NeZero.ne _) (pow_ne_zero _ (pole_units (ha' i)).1))

end
end ZInQBlueprint.ClusterRoots
#print axioms ZInQBlueprint.ClusterRoots.root_iff
#print axioms ZInQBlueprint.ClusterRoots.zero_fibre
#print axioms ZInQBlueprint.ClusterRoots.pole_fibre
