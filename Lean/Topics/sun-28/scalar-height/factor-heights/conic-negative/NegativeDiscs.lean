import NegativeQuartics
import Mathlib.Data.ZMod.Basic

namespace Sun28.ConicNegative
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def width {R : Type*} [CommRing R] (a b:R) : R := b^2+6*a^2
def numerator {R : Type*} [CommRing R] (a b:R) : R :=
  25*(width a b)^2-3528*(b^2-6*a^2)*(2*a*b)+2303*(b^2-6*a^2)^2

private def squares (m:ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ.image fun x : ZMod m => x*x

private def test (m p:ℕ) [NeZero m] (a b:ZMod m) : Prop :=
  (a.val%p≠0 ∨ b.val%p≠0) ∧ Q₀ a b∈squares m ∧ Q₁ a b∈squares m ∧ Q₂ a b∈squares m

private def good (m p:ℕ) [NeZero m] : Prop :=
  ∀ a b : ZMod m, test m p a b →
    (120*(width a b)^2:ZMod m).val%p ≠ 0 ∧ numerator a b=480*(width a b)^2

private instance (m p:ℕ) [NeZero m] : Decidable (good m p) := by unfold good test;infer_instance

private lemma finite_17 : good 17 17 := by decide
private lemma finite_19 : good 19 19 := by decide

private def good25 : Prop := ∀ a b : ZMod 25, test 25 5 a b →
  (width a b).val%5≠0 ∧ ∃u : ZMod 25, a=u*b ∧ (u=21 ∨ u=24)

private instance : Decidable good25 := by unfold good25 test;infer_instance

private lemma finite_25 : good25 := by decide

private lemma local_test {m p:ℕ} [NeZero m] (pp:p.Prime) (div:p∣m) (a b:ℤ)
    (cop : a.natAbs.Coprime b.natAbs) (g₀:IsSquare (Q₀ a b))
    (g₁:IsSquare (Q₁ a b)) (g₂:IsSquare (Q₂ a b)) : test m p a b := by
  refine ⟨?_,?_,?_,?_⟩
  · by_contra! z
    have cv (v:ℤ) (h:((v:ZMod m).val)%p=0) : (p:ℤ)∣v := by
      have hp:(p:ℤ)∣(m:ℤ):=by exact_mod_cast div
      have hv:=ZMod.val_intCast (n:=m) v
      have em:((v:ZMod m).val:ℤ)%(p:ℤ)=0:=by exact_mod_cast h
      rw [hv,Int.emod_emod_of_dvd _ hp] at em
      exact Int.dvd_of_emod_eq_zero em
    exact Nat.not_coprime_of_dvd_of_dvd pp.one_lt
      (Int.natAbs_dvd_natAbs.mpr (cv a z.1)) (Int.natAbs_dvd_natAbs.mpr (cv b z.2)) cop
  · obtain ⟨z,e⟩:=g₀
    apply Finset.mem_image.mpr
    refine ⟨(z:ZMod m),Finset.mem_univ _,?_⟩
    have he:=congrArg (Int.castRingHom (ZMod m)) e
    simpa [Q₀] using he.symm
  · obtain ⟨z,e⟩:=g₁
    apply Finset.mem_image.mpr
    refine ⟨(z:ZMod m),Finset.mem_univ _,?_⟩
    have he:=congrArg (Int.castRingHom (ZMod m)) e
    simpa [Q₁] using he.symm
  · obtain ⟨z,e⟩:=g₂
    apply Finset.mem_image.mpr
    refine ⟨(z:ZMod m),Finset.mem_univ _,?_⟩
    have he:=congrArg (Int.castRingHom (ZMod m)) e
    simpa [Q₂] using he.symm

/-- At 17 and 19 the normalized numerator and denominator of s give the residue 4.
At modulus 25 only two affine parameter residues are left. -/
theorem certified_discs {s:ℚ} (hs:component s) (f:rationalFactors s) :
    ∃ a b:ℤ, 0<b ∧ a.natAbs.Coprime b.natAbs ∧
      120*s*((b:ℚ)^2+6*(a:ℚ)^2)^2=H a b ∧
      (∀m:ℕ, m=17 ∨ m=19 → (120*width a b^2:ℤ) % m ≠ 0 ∧
        (m:ℤ) ∣ numerator a b-480*width a b^2) ∧
      ∃u:ZMod 25, (a:ZMod 25)=u*(b:ZMod 25) ∧ (u=21 ∨ u=24) := by
  obtain ⟨a,b,bp,cp,e,g0,g1,g2⟩:=integral_quartics hs f
  refine ⟨a,b,bp,cp,e,?_,?_⟩
  · intro m hm
    have prime:m.Prime:= by rcases hm with rfl|rfl <;> decide
    let _ : NeZero m := ⟨prime.ne_zero⟩
    have gd : good m m := by rcases hm with rfl|rfl; exact finite_17; exact finite_19
    obtain ⟨nz,eq⟩:=gd _ _ (local_test prime (dvd_refl m) a b cp g0 g1 g2)
    have hzero : ((120*width a b^2:ℤ):ZMod m)≠0 := by
      intro h
      simp [width] at h
      simp [width,h] at nz
    have divis := ZMod.intCast_zmod_eq_zero_iff_dvd (numerator a b-480*width a b^2) m
    refine ⟨fun bad=>hzero ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (Int.dvd_of_emod_eq_zero bad)),divis.mp ?_⟩
    simp [numerator,width] at eq ⊢
    exact sub_eq_zero.mpr eq
  · exact (finite_25 _ _ (local_test (by decide : Nat.Prime 5) (by decide : 5∣25) a b cp g0 g1 g2)).2

end
end Sun28.ConicNegative
#print axioms Sun28.ConicNegative.certified_discs
