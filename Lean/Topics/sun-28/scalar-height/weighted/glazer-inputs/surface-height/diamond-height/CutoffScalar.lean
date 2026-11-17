import CutoffEuler
import CochainField

namespace ZInQBlueprint.DiamondHeight
open Sun28.FiveMarkUnits Sun28.Ordinary Sun28.HeightFibres
noncomputable section
set_option maxRecDepth 12000

private theorem powered_square {G K : Type*} [Group G] [CommGroup K]
    (S O : Finset ℕ) (e : ℕ) (dyadic : 0 < e)
    (small : ∀ p ∈ S, p.Prime ∧ p ≤ 2^e) (large : ∀ p ∈ O, p.Prime)
    (f : G → K) (δ : G →* K) (dy : ∀ g, (δ g)^2 = 1)
    (ι : ∀ p : ℕ, G →* (ZMod p)ˣ) (χ : ∀ p : ℕ, (ZMod p)ˣ →* K)
    (square : ∀ g, (f g)^2 = δ g * (∏ p ∈ S, χ p (ι p g)) * ∏ p ∈ O, χ p (ι p g)) :
    ∃ k : ℕ, Odd k ∧ ∀ g, ((f g)^k)^(2 * (2^e * largeUnitOrders O)) = 1 := by
  obtain ⟨k, odd, ann⟩ := bounded_character_orders (G := G) (K := K) S O e dyadic small large
  refine ⟨k, odd, fun g => ?_⟩
  have swap (z : K) (m : ℕ) : (z^k)^(2*m) = ((z^2)^k)^m := by
    simp only [← pow_mul]
    rw [← Nat.mul_assoc, Nat.mul_comm k 2]
  rw [swap, square g]
  exact ann δ dy ι χ g

private theorem cutoff_small (p : ℕ) (hp : p ∈ oldCutoff) : p.Prime ∧ p ≤ 2^17 := by
  obtain ⟨range, prime⟩ := Finset.mem_filter.mp hp
  exact ⟨prime, (Finset.mem_range.mp range).le.trans (by decide : 76177 ≤ 2^17)⟩

attribute [local irreducible] oldCutoff

/-- The odd twist keeps an inflated sign factor and shortens the scalar field
uniformly in the fixed cutoff. Its finite degree is measured on the new cochain. -/
theorem cutoff_scalar_choice (a b:ℤ) (L:IntermediateField ℚ Qbar)
    [IsGalois ℚ L] [FiniteDimensional ℚ L] (degree:Module.finrank ℚ L≤576)
    (F:InflatedSplitting (K:=ℂˣ) (AlgEquiv.restrictNormalHom L : GQ →* (L ≃ₐ[ℚ] L)))
    (sign : ∀x y,(F.factor x y)^2=1) (continuous : Continuous F.b)
    (dy:GQ →* ℂˣ) (dy2:∀ g,(dy g)^2=1)
    (ι : ∀ p:ℕ, GQ →* (ZMod p)ˣ) (χ : ∀ p:ℕ, (ZMod p)ˣ →* ℂˣ)
    (sq:∀g,(F.b g)^2=dy g*(∏p∈oldCutoff,χ p (ι p g))*∏p∈oddSupport a b,χ p (ι p g)) :
    ∃ k:ℕ, ∃ odd:Odd k, ∃ E:IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ IsGalois ℚ E ∧
      E.fixingSubgroup=(F.oddPower sign odd).restrict.ker.map (markingGroup L).subtype ∧
      Module.finrank ℚ E≤1152*2^17*largeUnitOrders (oddSupport a b) := by
  let S:=oldCutoff
  let O:=oddSupport a b
  have small (p:ℕ) (hp:p∈S) : p.Prime ∧ p≤2^17 := by
    exact cutoff_small p hp
  have large (p:ℕ) (hp:p∈O) := (mem_oldContactPrimes.mp hp).1
  obtain ⟨k,odd,all⟩:=powered_square S O 17 (by decide) small large (fun g : GQ => F.b g) dy dy2 ι χ sq
  let F':=F.oddPower sign odd
  let M:=2^17*largeUnitOrders O
  have Mpos:0<M:=Nat.mul_pos (by decide) (Finset.prod_pos (fun p hp=>by have := (large p hp).two_le;omega))
  let bL : markingGroup L →* ℂˣ := F'.restrict
  have power (x:markingGroup L) : (bL x)^(2*M)=1:=by
    exact all x.val
  let : (markingGroup L).Normal := (AlgEquiv.restrictNormalHom L : GQ →* (L ≃ₐ[ℚ] L)).normal_ker
  have norm : (bL.ker.map (markingGroup L).subtype).Normal :=
    normal_scalar_kernel _ bL (fun g x=>F'.restrict_conjugate g x _ rfl)
  have hc : Continuous bL:= (continuous.pow k).comp continuous_subtype_val
  let : NeZero (2*M) := ⟨(Nat.mul_pos (by decide) Mpos).ne'⟩
  let u : markingGroup L → rootsOfUnity (2*M) ℂ := fun x=>⟨bL x,(mem_rootsOfUnity ..).mpr (power x)⟩
  have uc : Continuous u:=hc.subtype_mk _
  have same : (bL.ker:Set (markingGroup L))=u ⁻¹' ({1}:Set (rootsOfUnity (2*M) ℂ)) :=
    Set.ext fun x=>⟨fun eqn=>Subtype.ext eqn,fun eqn=>congrArg Subtype.val eqn⟩
  have op : IsOpen ((bL.ker.map (markingGroup L).subtype : Subgroup GQ) : Set GQ) := by
    apply (marking_open L).isOpenMap_subtype_val (bL.ker:Set (markingGroup L))
    rw [same]
    exact (isOpen_discrete _).preimage uc
  let U : OpenSubgroup (Qbar ≃ₐ[ℚ] Qbar) := ⟨bL.ker.map (markingGroup L).subtype,op⟩
  let H : ClosedSubgroup (Qbar ≃ₐ[ℚ] Qbar) := ⟨U.toSubgroup,U.isClosed⟩
  let E := IntermediateField.fixedField (F:=ℚ) (E:=Qbar) H.toSubgroup
  have fixing : E.fixingSubgroup=H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  have dim : FiniteDimensional ℚ E := (InfiniteGalois.isOpen_iff_finite E).mp (by rw [fixing];exact op)
  have gal : IsGalois ℚ E := (InfiniteGalois.normal_iff_isGalois E).mp (by rw [fixing];exact norm)
  refine ⟨k,odd,E,dim,gal,fixing,?_⟩
  have agree : markingGroup E=E.fixingSubgroup := E.restrictNormalHom_ker
  rw [←marking_index E,agree,fixing]
  change (bL.ker.map (markingGroup L).subtype).index≤_
  rw [Subgroup.index_map_subtype]
  have ix:=character_index bL (Nat.mul_pos (by decide) Mpos) power
  calc
    _ ≤ (2*M)*576 := Nat.mul_le_mul ix ((marking_index L).trans_le degree)
    _ = _ := by dsimp only [M,O];ring

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.cutoff_scalar_choice
