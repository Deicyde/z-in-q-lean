import PrimePatternCRT
import FamilyLocal

namespace Sun28.TwistPrimes
open PairedClasses

/-- Keeping the index divisible by D prevents any prime of D from appearing
in the squarefree part. -/
private theorem avoided_factors {β k D θ h : ℕ} (hk : β<k^2) (dk : D∣k)
    (bd : β.Coprime D) (eq : (k^2-β)*(9*k^2-β)=θ*h^2) : θ.Coprime D := by
  by_contra nd
  obtain ⟨p,pp,pt,pD⟩ := Nat.Prime.not_coprime_iff_dvd.mp nd
  let : Fact p.Prime := ⟨pp⟩
  have pb : (β:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr
    (fun d=>pp.not_dvd_one (bd ▸ Nat.dvd_gcd d pD))
  have z := congrArg (fun n : ℕ => (n:ZMod p)) eq
  have nine : β≤9*k^2 := by omega
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hk.le,Nat.cast_sub nine,Nat.cast_ofNat] at z
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr (pD.trans dk),
    (ZMod.natCast_eq_zero_iff _ _).mpr pt] at z
  exact mul_ne_zero pb pb (by simpa using z)

private theorem index_family {β k θ h : ℕ} (hk : β<k^2)
    (eq : (k^2-β)*(9*k^2-β)=θ*h^2) : Family β θ := by
  have nine : β<9*k^2 := by omega
  have pos : 0<θ*h^2 := eq ▸ Nat.mul_pos (Nat.sub_pos_of_lt hk) (Nat.sub_pos_of_lt nine)
  have hne : h≠0 := by rintro rfl; simp at pos
  refine ⟨k,h,by exact_mod_cast hne,?_⟩
  have e := congrArg (fun n : ℕ => (n:ℚ)) eq
  simpa only [Nat.cast_mul,Nat.cast_sub hk.le,Nat.cast_sub nine.le,Nat.cast_pow,Nat.cast_ofNat] using e

/-- The two witnesses here use the literal same twist parameter n=β. -/
theorem fixed_points_of_family {β θ : ℕ} (hb : 0<β) (ht : 0<θ) (fam : Family β θ) :
    PreparedPoles.TwistPoint β β ∧ PreparedPoles.TwistPoint β (β*θ) := by
  obtain ⟨k,y,hy,e⟩ := fam
  have bp : 0<(β:ℚ) := by exact_mod_cast hb
  have H : 3*k^2+(β:ℚ)≠0 := ne_of_gt (by positivity)
  refine ⟨⟨1,0,one_ne_zero,by norm_num⟩,(twist_iff_quartic hb (Nat.mul_pos hb ht)).mpr ?_⟩
  refine ⟨3*k^2-β,2*k,(y*(3*k^2+β))⁻¹,?_⟩
  push_cast
  rw [quartic_specialization,e]
  field_simp

/-- For every sufficiently unrestricted prime pattern there are arbitrarily large
admissible outputs of the integral quartic. Each prescribed prime divides its
squarefree part and does not divide its square factor. The two rational points
are produced with n equal to β. -/
theorem prescribed_unbounded {β D : ℕ} (hb : 0<β) (sb : Squarefree β)
    (b6 : β.Coprime 6) (bm : β%24=17) (hd : 0<D) (bd : β.Coprime D)
    (S : Finset ℕ) (split : ∀ p ∈ S, SplitRoot β p) (avoid : ∀ p ∈ S, ¬p∣D) (B : ℕ) :
    ∃ θ k h : ℕ, B<θ ∧ β<k^2 ∧ (k^2-β)*(9*k^2-β)=θ*h^2 ∧ AdmissiblePair β θ ∧
      θ.Coprime D ∧ (∀ p ∈ S, p∣θ ∧ ¬p∣h) ∧
      PreparedPoles.TwistPoint β β ∧ PreparedPoles.TwistPoint β (β*θ) := by
  classical
  obtain ⟨p,large,ready⟩ := fresh_split hb (max B D)
  let U := insert p S
  have available (q : ℕ) (m : q∈U) : SplitRoot β q := by
    rcases Finset.mem_insert.mp m with rfl|old
    · exact ready
    · exact split q old
  have allowed (q : ℕ) (m : q∈U) : ¬q∣D := by
    rcases Finset.mem_insert.mp m with rfl|old
    · exact Nat.not_dvd_of_pos_of_lt hd (lt_of_le_of_lt (le_max_right _ _) large)
    · exact avoid q old
  obtain ⟨k,hk,six,dk,bk,roots⟩ := prescribed_index hb hd b6 bd U available allowed
  obtain ⟨θ,h,eq,adm,_⟩ := family_of_index hb hk sb b6 bk bm six
  have hit (q : ℕ) (m : q∈U) : q∣θ ∧ ¬q∣h := forced_factor hk (available q m) (roots q m) eq
  have pt := (hit p (Finset.mem_insert_self p S)).1
  have ltθ := (lt_of_le_of_lt (le_max_left B D) large).trans_le (Nat.le_of_dvd adm.2.1 pt)
  exact ⟨θ,k,h,ltθ,hk,eq,adm,avoided_factors hk dk bd eq,
    fun q m=>hit q (Finset.mem_insert_of_mem m),fixed_points_of_family hb adm.2.1 (index_family hk eq)⟩

/-- Infinitude holds separately on every admissible β-fibre. -/
theorem infinitely_many {β : ℕ} (hb : 0<β) (sb : Squarefree β) (b6 : β.Coprime 6)
    (bm : β%24=17) :
    Set.Infinite {θ : ℕ | AdmissiblePair β θ ∧ Family β θ} := by
  classical
  intro fin
  let T := fin.toFinset
  obtain ⟨θ,k,h,large,hk,eq,adm,_⟩ := prescribed_unbounded hb sb b6 bm
    (by decide : 0<1) (Nat.coprime_one_right _) ∅ (by simp) (by simp) (T.sup id)
  have m : θ∈T := fin.mem_toFinset.mpr ⟨adm,index_family hk eq⟩
  exact (not_lt_of_ge (Finset.le_sup (f:=id) m)) large

end Sun28.TwistPrimes
#print axioms Sun28.TwistPrimes.fixed_points_of_family
#print axioms Sun28.TwistPrimes.prescribed_unbounded
#print axioms Sun28.TwistPrimes.infinitely_many
