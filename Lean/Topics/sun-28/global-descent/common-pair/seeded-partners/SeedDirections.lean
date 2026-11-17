import SeedResidues
import PrimePatternCRT

namespace Sun28.SeededPartners
open Sun28.TwistPrimes Sun28.PairedClasses

theorem choose_index {b d : ℕ} (ad : AdmissiblePair b d) (B : ℕ) :
    ∃ k p : ℕ, b<k^2 ∧ 3*d∣k ∧ b.Coprime k ∧ (k:ZMod 128)^2=(b:ZMod 128)+96 ∧
      B<p ∧ SplitRoot b p ∧ SimpleRoot b p k := by
  obtain ⟨bp,dp,_,_,bd,b6,_,bm,dm,_⟩ := ad
  obtain ⟨p,larg,sp⟩ := fresh_split bp (max B d)
  have big : B<p := (le_max_left _ _).trans_lt larg
  have pd : ¬p∣d := Nat.not_dvd_of_pos_of_lt dp ((le_max_right _ _).trans_lt larg)
  obtain ⟨x,_,six,dx,bx,hx⟩ := prescribed_index bp dp b6 bd {p}
    (by intro v h;rcases Finset.mem_singleton.mp h with rfl;exact sp)
    (by intro v h;rcases Finset.mem_singleton.mp h with rfl;exact pd)
  have S := hx p (Finset.mem_singleton_self _)
  have good2 : ¬2∣3*d*b*p^2 := by
    have nod : ¬2∣d := by omega
    have nob : ¬2∣b := by omega
    have notp : ¬2∣p := fun h => sp.2.1 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two sp.1).mp h ▸ (dvd_mul_of_dvd_left (by decide : 2∣6) b))
    intro H
    simp only [Nat.prime_two.dvd_mul] at H
    rcases H with ((h|h)|h)|h
    · omega
    · exact nod h
    · exact nob h
    · exact notp (Nat.prime_two.dvd_of_dvd_pow h)
  let M:=3*d*b*p^2
  have hcop : M.Coprime 128 := (Nat.prime_two.coprime_iff_not_dvd.mpr good2).symm.pow_right 7
  obtain ⟨r,dy⟩ := choose_dyadic b (by omega)
  let z := Nat.chineseRemainder hcop x r
  let k := z.val+(b+1)*(M*128)
  have move : k ≡ z.val [MOD M*128] := Nat.add_mul_modulus_modEq_iff.mpr (Nat.ModEq.refl _)
  have same : k ≡ x [MOD M] :=
    (move.of_dvd (dvd_mul_right _ _)).trans (by simpa [z] using z.prop.1)
  have modtwo : k ≡ r [MOD 128] := (move.of_dvd (dvd_mul_left _ _)).trans z.prop.2
  have hM : 0<M := by dsimp [M];exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) dp) bp) (pow_pos sp.1.pos _)
  have low : b<k := by
    have H := Nat.mul_le_mul_left (b+1) (show 1≤M*128 by omega)
    dsimp only [k];omega
  have eqk : (k:ZMod 128)=(r:ZMod 128) := (ZMod.natCast_eq_natCast_iff ..).mpr modtwo
  have sameb := same.of_dvd (show b∣M from dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  have cp : b.Coprime k := by rwa [Nat.coprime_comm,Nat.Coprime,sameb.gcd_eq,←Nat.Coprime,Nat.coprime_comm]
  have p2 := same.of_dvd (show p^2∣M from dvd_mul_left _ _)
  have divided : 3*d∣x := by
    have : 6∣x := six
    have cop3 : (3:ℕ).Coprime d := Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
    exact cop3.mul_dvd_of_dvd_of_dvd ((by decide : 3∣6).trans this) dx
  refine ⟨k,p,by nlinarith,?_,cp,by rwa [eqk],big,sp,?_,?_⟩
  · exact ((same.of_dvd (show 3*d∣M from (dvd_mul_right _ _).trans (dvd_mul_right _ _))).dvd_iff (dvd_refl _)).mpr divided
  · exact ((p2.of_dvd (dvd_pow_self _ (by decide : 2≠0))).pow 2).trans S.1
  · exact fun e => S.2 ((p2.pow 2).symm.trans e)

end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.choose_index
