import PicardLocalization
import AbelianPowers

/-! The split integral genus-two case of Dokchitser–Dokchitser–Maistret–Morgan,
Theorem 10.3(5), and its application to the actual Picard Jacobian. The published
implication is an explicit argument. The calculation of its cluster hypotheses
and the transport of the resulting abelian model are proved below. -/

open CategoryTheory Polynomial IsDiscreteValuationRing
open ZInQBlueprint.AbelianModel
open ZOverQ.Qualitative.Picard.Assembly
open ZOverQ.Qualitative.LocalSupport ZOverQ.Qualitative.PicardLocalization
open ZOverQ.Qualitative.PicardDescent ZOverQ.Qualitative.PicardConjugation
open ZInQ ZInQ.QualitativeHeight

namespace ZOverQ.Qualitative.PicardGoodReduction
noncomputable section

/-- Nonempty closed discs on six labelled roots. Recentring a disc at a root in
it and taking its least attained pairwise valuation gives this finite list. -/
def rootBall {Γ : Type*} [LinearOrder Γ] (dist : Index → Index → Γ) (b r : Index) : Cluster :=
  Finset.univ.filter fun i => dist r b ≤ dist i b

def clusterTree {Γ : Type*} [LinearOrder Γ] (dist : Index → Index → Γ) : Finset Cluster :=
  Finset.univ.biUnion fun b => Finset.univ.image (rootBall dist b)

/-- Any nonempty root-centred threshold has a boundary value attained at a root. -/
theorem rootBall_of_threshold {Γ : Type*} [LinearOrder Γ] (dist : Index → Index → Γ)
    (b : Index) (d : Γ) (h : ∃ r, d ≤ dist r b) :
    ∃ r, (Finset.univ.filter fun i => d ≤ dist i b) = rootBall dist b r := by
  let S := Finset.univ.filter fun i => d ≤ dist i b
  have hn : S.Nonempty := by obtain ⟨r,hr⟩ := h; exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩
  obtain ⟨r,hr,hmin⟩ := Finset.exists_min_image S (fun i => dist i b) hn
  refine ⟨r,?_⟩
  ext i
  simp only [rootBall,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun hi => hmin _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩),
    fun hi => (Finset.mem_filter.mp hr).2.trans hi⟩

/-- The computed finite tree is exactly the nonempty intersections with valuation
balls, allowing the radius `⊤` for a one-point ball. This applies equally after
prolonging the valuation to the algebraic closure. -/
theorem disc_iff_mem {K Γ : Type*} [CommRing K] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation K Γ) (x : Index → K) (s : Cluster) :
    (s.Nonempty ∧ ∃ (z : K) (d : Γ), s = Finset.univ.filter (fun i => d ≤ v (x i-z))) ↔
      s ∈ clusterTree (fun i j => v (x i-x j)) := by
  constructor
  · rintro ⟨⟨b,hb⟩,z,d,rfl⟩
    have h : d ≤ v (x b-z) := (Finset.mem_filter.mp hb).2
    have recenter : (Finset.univ.filter fun i => d ≤ v (x i-z)) =
        Finset.univ.filter fun i => d ≤ v (x i-x b) := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro h'
        have hz : d ≤ v (z-x b) := by rwa [v.map_sub_swap]
        simpa only [sub_add_sub_cancel] using v.map_le_add h' hz
      · intro h'
        simpa only [sub_add_sub_cancel] using v.map_le_add h' h
    have hn : ∃ r, d ≤ v (x r-x b) := ⟨b,by simp⟩
    obtain ⟨r,hr⟩ := rootBall_of_threshold (fun i j => v (x i-x j)) b d hn
    rw [recenter,hr]
    exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,Finset.mem_image_of_mem _ (Finset.mem_univ r)⟩
  · intro h
    obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp h
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hb
    exact ⟨⟨b,by simp [rootBall]⟩,x b,v (x r-x b),rfl⟩

/-- The principal-cluster exceptions for an even degree-six equation of genus two. -/
def picturePrincipal (P : Finset Cluster) (s : Cluster) : Prop :=
  let children := P.filter fun t => t ⊂ s ∧ ∀ u ∈ P, ¬(t ⊂ u ∧ u ⊂ s)
  s ∈ P ∧ 3 ≤ s.card ∧ ¬(s = Finset.univ ∧ Even s.card ∧ children.card = 2) ∧
    ∀ t ∈ children, t.card ≠ 4

/-- The normalized order of the leading coefficient plus the six join depths. -/
def pictureNu (P : Finset Cluster) (lead : ℤ) (dist : Index → Index → ℕ∞) (s : Cluster) : ℤ :=
  lead + ∑ r : Index, ((depth dist ((P.filter (fun t => s ⊆ t ∧ r ∈ t)).inf id)).toNat : ℤ)

private abbrev wittCharZero (p : ℕ) [Fact p.Prime] (k : Subfield (Residues p)) :
    CharZero (WittVector p k) :=
  charZero_of_injective_ringHom (f := fromPadics p k)
    ((WittVector.map_injective _ (ZMod.castHom (by simp) k).injective).comp (WittVector.equiv p).symm.injective)

/-- Sufficiency in Theorem 10.3(5) of *Arithmetic of hyperelliptic curves over
local fields* (doi:10.1007/s00208-021-02319-y), for an arbitrary separable
integral sextic whose roots split over the given finite unramified local field.
The roots in its Witt ring have integral pairwise valuations and trivial inertia.
The conclusion is an abelian model of the Jacobian of its smooth proper completion. -/
def SplitSexticDDMM : Prop := ∀ (p : ℕ) [Fact p.Prime], 2 < p →
  ∀ (k : Subfield (Residues p)) [Finite k],
  letI := wittCharZero p k
  let S := WittVector p k
  let K := FractionRing S
  ∀ (f : S[X]) (x : Index → S),
    f.Splits → (∀ w, f.IsRoot w ↔ ∃ i, x i = w) →
    let dist := fun i j => addVal S (x i - x j)
    let P := clusterTree dist
    (∀ s ∈ P, s ≠ Finset.univ → Odd s.card) →
    (∀ s, picturePrincipal P s → Even (pictureNu P ((addVal S f.leadingCoeff).toNat : ℤ) dist s)) →
    ∀ (dg : (f.map (algebraMap S K)).natDegree = 6) (sg : (f.map (algebraMap S K)).Separable),
      GoodWitt p k (completionJacobian _ dg sg)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
private theorem tree_one : ∀ A : Finset (Fin 2), clusterTree (distances A (1:ℕ∞)) = tree A := by decide

private theorem tree_pos (A : Finset (Fin 2)) (m : ℕ) (h : 0 < m) :
    clusterTree (distances A (m:ℕ∞)) = tree A := by
  have hpos : (0:ℕ∞) < (m:ℕ∞) := by exact_mod_cast h
  have compare (rb ib rr ri : Prop) [Decidable rb] [Decidable ib] [Decidable rr] [Decidable ri] :
      (if rb then (⊤:ℕ∞) else if rr then (m:ℕ∞) else 0) ≤ (if ib then ⊤ else if ri then (m:ℕ∞) else 0) ↔
      (if rb then (⊤:ℕ∞) else if rr then 1 else 0) ≤ (if ib then ⊤ else if ri then 1 else 0) := by
    by_cases a : rb <;> by_cases b : ib <;> by_cases c : rr <;> by_cases d : ri <;> simp_all
    exact h.ne'
  have eqball : rootBall (distances A (m:ℕ∞)) = rootBall (distances A (1:ℕ∞)) := by
    funext b r
    apply Finset.ext
    intro i
    simp only [rootBall,Finset.mem_filter,Finset.mem_univ,true_and]
    exact compare (r=b) (i=b) (r.1=b.1 ∧ r.1∈A) (i.1=b.1 ∧ i.1∈A)
  exact (congrArg (fun (B : Index → Index → Cluster) => Finset.univ.biUnion fun b =>
    Finset.univ.image (B b)) eqball).trans (tree_one A)

private theorem cluster_tests (A : Finset (Fin 2)) (m : ℕ) (lead : ℤ)
    (h : ∀ s, principal A s → Even (nu lead A (distances A (m:ℕ∞)) s)) :
    let dist := distances A (m:ℕ∞)
    let P := clusterTree dist
    (∀ s ∈ P, s ≠ Finset.univ → Odd s.card) ∧
      (∀ s, picturePrincipal P s → Even (pictureNu P lead dist s)) := by
  dsimp only
  by_cases hm : m = 0
  · subst m
    have dz (n : ℕ∞) : distances A (0:ℕ∞) = distances ∅ n := by
      funext i j
      simp [distances]
    have tr : clusterTree (distances A (0:ℕ∞)) = tree ∅ := by rw [dz 1,tree_one]
    rw [show (↑(0:ℕ):ℕ∞) = 0 by rfl,tr]
    refine ⟨proper_odd _,fun s hs => ?_⟩
    change principal ∅ s at hs
    rcases (principal_iff ∅ s).mp hs with ⟨rfl,_⟩ | ⟨i,hi,_⟩
    · change Even (nu lead ∅ (distances A 0) Finset.univ)
      rw [dz 0,show nu lead ∅ (distances ∅ 0) Finset.univ = lead by simpa only [Nat.cast_zero] using nu_top lead ∅ 0]
      by_cases hA : A = Finset.univ
      · have hi : (0 : Fin 2) ∈ A := hA ▸ Finset.mem_univ _
        have hr := h (row 0) ((principal_iff ..).mpr (Or.inr ⟨0,hi,rfl⟩))
        have hl : Even (lead+3*(0:ℤ)) := (nu_row lead A 0 hi) ▸ hr
        simpa only [mul_zero,add_zero] using hl
      · exact (nu_top lead A 0) ▸ h Finset.univ ((principal_iff ..).mpr (Or.inl ⟨rfl,hA⟩))
    · exact (Finset.notMem_empty _ hi).elim
  · rw [tree_pos A m (Nat.pos_of_ne_zero hm)]
    exact ⟨proper_odd A,h⟩

/-- An isomorphism of generic commutative group schemes transports its integral abelian model. -/
theorem goodWitt_of_iso {p : ℕ} [Fact p.Prime] {k : Subfield (Residues p)}
    {A B : GroupScheme (FractionRing (WittVector p k))} (i : A ≅ B) (h : GoodWitt p k A) :
    GoodWitt p k B := by
  obtain ⟨M,hM,⟨e⟩⟩ := h
  exact ⟨M,hM,⟨e ≪≫ i⟩⟩

/-- The named finite Witt model is good for the scalar extension of the global
family Jacobian with its actual twist and prescribed root of minus three. -/
def GoodLocalFiber {p : ℕ} [Fact p.Prime] (t : ℚ) (e : ℤ) (ht : t ∉ contactSet) (he : e ≠ 0)
    {q : PicardLocal.WittRing p} (D : FiniteSplitting p (picardParameter t).num (picardParameter t).den e q) : Prop :=
  letI : Finite D.field := D.finite
  letI := wittCharZero p D.field
  let S := WittVector p D.field
  let K := FractionRing S
  ∃ φ : fixedField →ₐ[ℚ] K, φ ρ = algebraMap S K D.rho ∧ GoodWitt p D.field
    ((baseChange φ.toRingHom).obj (familyJacobian t (e:ℚ) ht (by exact_mod_cast he)
      (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)))

/-- Apply the general published implication to the actual six roots and transfer its model. -/
theorem goodWitt_of_fibre (criterion : SplitSexticDDMM) (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (t : ℚ) (e : ℤ) (ht : t ∉ contactSet) (he : e ≠ 0) {q : PicardLocal.WittRing p}
    {A : Finset (Fin 2)} {m : ℕ} (D : FibreData p (picardParameter t).num (picardParameter t).den e q A m)
    (comparison : WittComparison t e ht he D.finiteModel) : GoodLocalFiber t e ht he D.finiteModel := by
  let k := D.finiteModel.field
  let : Finite k := D.finiteModel.finite
  let := wittCharZero p k
  let S := WittVector p k
  let s := picardParameter t
  let f := twisted s.num s.den e D.finiteModel.rho
  obtain ⟨φ,hφ,df,sf,⟨iso⟩⟩ := comparison
  obtain ⟨T,_,exh,par⟩ := finite_configuration p D
  let dist := fun i j => addVal S (T.point i-T.point j)
  let lead : ℤ := (addVal S f.leadingCoeff).toNat
  have vals : dist = distances A (m:ℕ∞) := by
    funext i j
    calc
      _ = distances A ((addVal S) ((p:S)^m)) i j :=
        pairwise_valuations T (RingHom.id S) (addVal S) addVal_eq_zero_of_unit i j
      _ = _ := congrArg (fun n => distances A n i j) ((show Irreducible (p:S) from WittVector.irreducible p).addVal_pow m)
  have tests : (∀ s ∈ clusterTree dist, s ≠ Finset.univ → Odd s.card) ∧
      (∀ s, picturePrincipal (clusterTree dist) s → Even (pictureNu (clusterTree dist) lead dist s)) := by
    rw [vals]
    exact cluster_tests A m lead (fun s hs => (vals ▸ par s hs))
  exact ⟨φ,hφ,goodWitt_of_iso iso.symm
    (criterion p (by omega) k f T.point D.finiteModel.splits exh tests.1 tests.2 df sf)⟩

private theorem twist_nonzero (s : ℚ) : (PrimitiveTwist.twist s : ℤ) ≠ 0 := by
  exact_mod_cast (PrimitiveTwist.positive s).ne'

/-- For each noncontact rational fibre and each even branch valuation at `p > 3`,
the published theorem gives an abelian scheme over the particular finite unramified
Witt ring, whose generic fibre is the base change of the global family Jacobian. -/
theorem family_goodWitt (criterion : SplitSexticDDMM) (p : ℕ) [Fact p.Prime] (hp : 3 < p) (t : ℚ)
    (ht : t ∉ contactSet) (hev : ¬ Odd (padicValRat p (primitiveBranch (picardParameter t)))) :
    let s := picardParameter t
    let e : ℤ := PrimitiveTwist.twist s
    ∃ (q : PicardLocal.WittRing p) (A : Finset (Fin 2)) (m : ℕ) (D : FibreData p s.num s.den e q A m),
      q^2 = -3 ∧ GoodLocalFiber t e ht (twist_nonzero s) D.finiteModel := by
  obtain ⟨q,A,m,D,hq,comparison⟩ := family_local_cluster_jacobian p hp t ht hev
  exact ⟨q,A,m,D,hq,goodWitt_of_fibre criterion p hp t _ ht (twist_nonzero _) D comparison⟩

/-- A surjective morphism from a positive power of the local Jacobian to the
base change of the specified rational abelian variety. `power J n` has `n+1` factors. -/
def LocalPowerQuotient (p : ℕ) [Fact p.Prime] (k : Subfield (Residues p)) [Finite k]
    (J : GroupScheme (FractionRing (WittVector p k))) (n : ℕ) (B : GroupScheme ℚ) : Prop :=
  letI := wittFractionAlgebra p k
  ∃ f : AbelianPowers.power J n ⟶ (baseChange (algebraMap ℚ_[p] (FractionRing (WittVector p k)))).obj
      ((baseChange (algebraMap ℚ ℚ_[p])).obj B), AlgebraicGeometry.Surjective f.hom.hom.hom.left

private theorem completion_congr {K : Type} [Field K] [CharZero K] {f g : K[X]} (h : f = g)
    (df : f.natDegree = 6) (sf : f.Separable) (dg : g.natDegree = 6) (sg : g.Separable) :
    Nonempty (completionJacobian f df sf ≅ completionJacobian g dg sg) := by
  subst g
  exact ⟨Iso.refl _⟩

/-- Any embedding taking the distinguished radical to the chosen Witt lift has the same
local Jacobian. Its actual local power quotient gives good reduction over `ℚ_p` by Serre–Tate. -/
theorem reduction_of_fibre_power (criterion : SplitSexticDDMM) (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (st : SerreTateAt p) {B : GroupScheme ℚ} (hB : IsAbelianScheme B)
    (t : ℚ) (e : ℤ) (ht : t ∉ contactSet) (he : e ≠ 0) {q : PicardLocal.WittRing p} (hq : q^2 = -3)
    {A : Finset (Fin 2)} {m : ℕ} (D : FibreData p (picardParameter t).num (picardParameter t).den e q A m) :
    let k := D.finiteModel.field
    letI : Finite k := D.finiteModel.finite
    letI := wittCharZero p k
    let S := WittVector p k
    let K := FractionRing S
    let J := familyJacobian t (e:ℚ) ht (by exact_mod_cast he) (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
    ∀ (φ : fixedField →ₐ[ℚ] K), φ ρ = algebraMap S K D.finiteModel.rho → ∀ n : ℕ,
      LocalPowerQuotient p k ((baseChange φ.toRingHom).obj J) n B → GoodReductionAt p B := by
  let k := D.finiteModel.field
  let : Finite k := D.finiteModel.finite
  let := wittCharZero p k
  let S := WittVector p k
  let K := FractionRing S
  let s := picardParameter t
  let hd : (e:ℚ) ≠ 0 := by exact_mod_cast he
  let J := familyJacobian t (e:ℚ) ht hd (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
  change ∀ (φ : fixedField →ₐ[ℚ] K), φ ρ = algebraMap S K D.finiteModel.rho → ∀ n : ℕ,
    LocalPowerQuotient p k ((baseChange φ.toRingHom).obj J) n B → GoodReductionAt p B
  intro φ hφ n onto
  obtain ⟨ψ,hψ,model⟩ := goodWitt_of_fibre criterion p hp t e ht he D (finite_splitting_jacobian p hp t e ht he hq _)
  obtain ⟨dψ,sψ,⟨iψ⟩⟩ := family_primitive_jacobian ψ.toRingHom t e ht he
  obtain ⟨dφ,sφ,⟨iφ⟩⟩ := family_primitive_jacobian φ.toRingHom t e ht he
  have eqf := congrArg (twisted s.num s.den e) (hψ.trans hφ.symm)
  obtain ⟨a⟩ := completion_congr eqf dψ sψ dφ sφ
  have good := goodWitt_of_iso (iψ ≪≫ a ≪≫ iφ.symm) model
  have hJ : IsAbelianScheme J := by
    unfold J familyJacobian
    apply jacobian_is_abelian
  exact AbelianPowers.reduction_of_power p st hB k n _ (isAbelianScheme_baseChange φ.toRingHom hJ) good onto

private theorem cast_twist_nonzero (s : ℚ) : ((PrimitiveTwist.twist s : ℤ) : ℚ) ≠ 0 := by
  exact_mod_cast twist_nonzero s

/-- For each noncontact fibre and every even branch valuation, there is one explicitly
identified finite Witt splitting field and embedding over which a local power quotient
of the actual Jacobian suffices for good reduction of the rational factor. -/
theorem family_reduction_of_power (criterion : SplitSexticDDMM) (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (st : SerreTateAt p) (t : ℚ) (ht : t ∉ contactSet)
    (hev : ¬ Odd (padicValRat p (primitiveBranch (picardParameter t)))) :
    let s := picardParameter t
    let e : ℤ := PrimitiveTwist.twist s
    ∃ (q : PicardLocal.WittRing p) (A : Finset (Fin 2)) (m : ℕ) (D : FibreData p s.num s.den e q A m),
      let k := D.finiteModel.field
      letI : Finite k := D.finiteModel.finite
      letI := wittCharZero p k
      let S := WittVector p k
      let K := FractionRing S
      let J := familyJacobian t (e:ℚ) ht (cast_twist_nonzero s) (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
      ∃ φ : fixedField →ₐ[ℚ] K, φ ρ = algebraMap S K D.finiteModel.rho ∧
        ∀ (B : GroupScheme ℚ), IsAbelianScheme B → ∀ (n : ℕ),
          LocalPowerQuotient p k ((baseChange φ.toRingHom).obj J) n B → GoodReductionAt p B := by
  let s := picardParameter t
  obtain ⟨q,A,m,D,hq,comp⟩ := family_local_cluster_jacobian p hp t ht hev
  obtain ⟨φ,hφ,_,_,_⟩ := comp
  exact ⟨q,A,m,D,φ,hφ,fun B hB => reduction_of_fibre_power criterion p hp st hB t _ ht (twist_nonzero s) hq D φ hφ⟩

#print axioms reduction_of_fibre_power
#print axioms family_reduction_of_power

#print axioms disc_iff_mem
#print axioms rootBall_of_threshold
#print axioms SplitSexticDDMM
#print axioms goodWitt_of_iso
#print axioms goodWitt_of_fibre
#print axioms family_goodWitt

end
end ZOverQ.Qualitative.PicardGoodReduction
