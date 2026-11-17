import PrimePatternCRT
namespace Sun28.PrescribedPoints
open TwistPrimes
private theorem seed : ∀ a : Fin 27, a.val%3=1 → ∃ s : Fin 54,
    2∣s.val ∧ s.val^2%27=(a.val+9)%27 := by decide

private theorem coprime54 {θ : ℕ} (t : θ%24=1) : θ.Coprime 54 := by
  apply Nat.coprime_of_dvd
  intro p pp pt pm
  have e : p=2 ∨ p=3 := by
    have : p∣2*3^3 := pm
    rcases pp.dvd_mul.mp this with d|d
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide)).mp d)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq pp (by decide)).mp (pp.dvd_of_dvd_pow d))
  rcases e with rfl|rfl <;> omega

theorem reverse_index {θ p : ℕ} (tp : 0<θ) (tm : θ%24=1) (sp : SplitRoot θ p) :
    ∃ s : ℕ, θ<s^2 ∧ 2∣s ∧ s^2 ≡ θ+9 [MOD 27] ∧ θ.Coprime s ∧ SimpleRoot θ p s := by
  obtain ⟨a,even,mod⟩:=seed ⟨θ%27,Nat.mod_lt _ (by decide)⟩ (by dsimp;omega)
  have am : a.val^2 ≡ θ+9 [MOD 27] := by change _%27=_%27;dsimp at mod;omega
  obtain ⟨r,rs⟩:=simple_root sp
  have pc : p.Coprime 54 := by
    apply sp.1.coprime_iff_not_dvd.mpr
    intro d
    have d' : p∣2*3^3:=d
    rcases sp.1.dvd_mul.mp d' with h|h
    · exact sp.2.1 (h.trans ⟨3*θ,by ring⟩)
    · exact sp.2.1 ((sp.1.dvd_of_dvd_pow h).trans ⟨2*θ,by ring⟩)
  have pθ : p.Coprime θ:=sp.1.coprime_iff_not_dvd.mpr
    (fun d=>sp.2.1 (dvd_mul_of_dvd_right d 6))
  let c:=Nat.chineseRemainder (coprime54 tm).symm a.val 1
  let d:=Nat.chineseRemainder ((pc.mul_right pθ).symm.pow_right 2) c.val r
  let E:=54*θ*p^2
  let s:=d.val+(θ+1)*E
  have ep : 0<E:=Nat.mul_pos (Nat.mul_pos (by decide) tp) (pow_pos sp.1.pos _)
  have lt : θ<s:=by have b:=Nat.mul_le_mul_left (θ+1) (show 1≤E by omega);dsimp [s];omega
  have mov : s ≡ d.val [MOD E]:=Nat.add_mul_modulus_modEq_iff.mpr (Nat.ModEq.refl _)
  have sc : s ≡ c.val [MOD 54*θ]:=(mov.of_dvd (dvd_mul_right _ _)).trans d.prop.1
  have sa : s≡a.val [MOD 54]:=(sc.of_dvd (dvd_mul_right _ _)).trans c.prop.1
  have st : s≡1 [MOD θ]:=(sc.of_dvd (dvd_mul_left _ _)).trans c.prop.2
  have sr : s^2≡r^2 [MOD p^2]:=((mov.of_dvd (dvd_mul_left _ _)).trans d.prop.2).pow 2
  refine ⟨s,by nlinarith,(sa.dvd_iff (by decide : 2∣54)).mpr even,
    ((sa.of_dvd (by decide : 27∣54)).pow 2).trans am,?_,
    (sr.of_dvd (dvd_pow_self p (by decide : 2≠0))).trans rs.1,fun z=>rs.2 (sr.symm.trans z)⟩
  simpa [Nat.Coprime,Nat.gcd_comm θ s] using st.gcd_eq
end Sun28.PrescribedPoints
#print axioms Sun28.PrescribedPoints.reverse_index
