import ScalarExclusions

namespace Sun28.ScalarQuotients
open Sun28.WitnessHeight
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-- The local test depends only on the residue of its signed right side. -/
private theorem local_congr {d e:ℤ} {p n:ℕ} [NeZero n] (h:p∣n) (eq:(d:ZMod n)=(e:ZMod n))
    (C:Finset (ℕ×ℕ)) : localPairs p n h d C=localPairs p n h e C := by
  unfold localPairs;rw [eq]

private theorem coprime_rows {a b d:ℤ} (ab:a.natAbs.Coprime b.natAbs)
    (ns:∀p:ℕ,p.Prime → p∣d.natAbs → 2<p ∧ ¬IsSquare (-1:ZMod p) ∧ ¬IsSquare (-6:ZMod p)) :
    (2*a^2+3*b^2).natAbs.Coprime d.natAbs ∧ (a^2+b^2).natAbs.Coprime d.natAbs := by
  have lemma' (p:ℕ) (pp:p.Prime) (pd:p∣d.natAbs) :
      ¬(p:ℤ)∣2*a^2+3*b^2 ∧ ¬(p:ℤ)∣a^2+b^2 := by
    let _:Fact p.Prime:=⟨pp⟩
    obtain ⟨big,i,s⟩:=ns p pp pd
    have two:(2:ZMod p)≠0:=by
      intro z
      have t:(p:ℤ)∣2:=(ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa only [Int.cast_ofNat] using z)
      have q:p∣2:=by exact_mod_cast t
      have l:=Nat.le_of_dvd (by decide:0<2) q;omega
    have prim:¬((a:ZMod p)=0 ∧ (b:ZMod p)=0):=by
      rintro ⟨a0,b0⟩
      have pa:=(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp a0
      have pb:=(ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp b0
      exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt (by simpa using Int.natAbs_dvd_natAbs.mpr pa)
        (by simpa using Int.natAbs_dvd_natAbs.mpr pb)) ab
    constructor <;> intro h
    · have hf:2*(a:ZMod p)^2+3*(b:ZMod p)^2=0:=by
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
      by_cases bz:(b:ZMod p)=0
      · simp [bz,two] at hf
        exact prim ⟨hf,bz⟩
      apply s
      refine ⟨2*(a:ZMod p)/(b:ZMod p),?_⟩
      field_simp;linear_combination -2*hf
    · have hf:(a:ZMod p)^2+(b:ZMod p)^2=0:=by
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
      by_cases bz:(b:ZMod p)=0
      · simp [bz] at hf
        exact prim ⟨hf,bz⟩
      apply i
      refine ⟨(a:ZMod p)/(b:ZMod p),?_⟩
      field_simp;linear_combination -hf
  constructor
  · apply Nat.coprime_of_dvd
    intro p pp pd dn
    exact (lemma' p pp dn).1 (Int.natAbs_dvd_natAbs.mp (by simpa using pd))
  · apply Nat.coprime_of_dvd
    intro p pp pd dn
    exact (lemma' p pp dn).2 (Int.natAbs_dvd_natAbs.mp (by simpa using pd))

/-- For this entire family the first two kernels carry no primes of the twist. -/
theorem inert_twists_excluded {x y:ℚ} {d:ℤ} (sf:Squarefree d) (dy:Odd d) (d3:d%3=1)
    (ns:∀p:ℕ,p.Prime → p∣d.natAbs → 2<p ∧ ¬IsSquare (-1:ZMod p) ∧ ¬IsSquare (-6:ZMod p))
    (yn:y≠0) : octic x≠(d:ℚ)*y^2 := by
  intro eq
  obtain ⟨Y,e⟩:=integral_point sf yn eq
  have ab:x.num.natAbs.Coprime (x.den:ℤ).natAbs:=by simpa using x.reduced
  obtain ⟨k,l,u,v,hk,hl,ek,el⟩:=two_kernels ab (by exact_mod_cast x.den_nz) sf.ne_zero e
  obtain ⟨A,B⟩:=coprime_rows ab ns
  have km:k∣(2*x.num^2+3*(x.den:ℤ)^2).natAbs:=by
    rw [ek,Int.natAbs_mul];simp
  have lm:l∣(x.num^2+(x.den:ℤ)^2).natAbs:=by rw [el,Int.natAbs_mul];simp
  have kp:k∣14:=(A.of_dvd_left km).dvd_of_dvd_mul_right hk
  have lp:l∣30:=(B.of_dvd_left lm).dvd_of_dvd_mul_right hl
  have can:(k,l)∈candidates 1:=by
    apply Finset.mem_product.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨by simpa using kp,by decide⟩,Nat.mem_divisors.mpr ⟨by simpa using lp,by decide⟩⟩
  have first:=mem_localPairs ab e ek el 2 16 (by decide) (by decide) can
  have second:=local_congr (d:=d) (e:=d%16) (p:=2) (n:=16) (by decide)
    (by simpa only [Nat.cast_ofNat] using (ZMod.intCast_mod d 16).symm) (candidates 1)
  have table:∀ n:Fin 16, n.val%2=1 → localPairs 2 16 (by decide) (n.val:ℤ) (candidates 1)={(2,1)}:=by decide
  let j:Fin 16:=⟨(d%16).toNat,by omega⟩
  have je:(j.val:ℤ)=d%16:=by dsimp [j];omega
  obtain ⟨t,dt⟩:=dy
  have oddj:j.val%2=1:=by omega
  rw [second,←je,table j oddj] at first
  have next:=mem_localPairs ab e ek el 3 9 (by decide) (by decide) first
  let r:Fin 9:=⟨(d%9).toNat,by omega⟩
  have re:(r.val:ℤ)=d%9:=by dsimp [r];omega
  have rt:r.val%3=1:=by omega
  have tab:∀ z:Fin 9, z.val%3=1 → localPairs 3 9 (by decide) (z.val:ℤ) {(2,1)}=∅:=by decide
  have sub:=local_congr (d:=d) (e:=d%9) (p:=3) (n:=9) (by decide)
    (by simpa only [Nat.cast_ofNat] using (ZMod.intCast_mod d 9).symm) {(2,1)}
  rw [sub,←re,tab r rt] at next
  exact Finset.notMem_empty _ next

end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.inert_twists_excluded
