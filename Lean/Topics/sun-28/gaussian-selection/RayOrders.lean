import GaussianHeader

namespace Sun28.GaussianSelection
open ManuscriptV15.Arithmetic

private theorem nat_norm (z : Gaussian) (e : Bool) :
    (adjacentNorm z e : ℤ)=(z.1+(if e then 1 else -1))^2+z.2^2 := by
  unfold adjacentNorm gaussianNorm
  rw [Int.natCast_natAbs,abs_of_nonneg (by positivity)]

theorem ray_seven {z : Gaussian} (hz : gaussianCongruent 7 z (1,3)) :
    (adjacentNorm z true:ℤ) ≡ 6 [ZMOD 7] ∧ (adjacentNorm z false:ℤ) ≡ 2 [ZMOD 7] := by
  obtain ⟨x,y⟩:=hz
  change z.1 ≡ 1 [ZMOD 7] at x
  change z.2 ≡ 3 [ZMOD 7] at y
  constructor
  · rw [nat_norm]
    exact (((x.add (Int.ModEq.refl 1)).pow 2).add (y.pow 2)).trans (by decide)
  · rw [nat_norm]
    exact (((x.add (Int.ModEq.refl (-1))).pow 2).add (y.pow 2)).trans (by decide)

theorem ray_dyadic {z : Gaussian} (hz : gaussianCongruent 16 z (9,0)) :
    padicValNat 2 (adjacentNorm z true)=2 ∧ padicValNat 2 (adjacentNorm z false)=6 := by
  obtain ⟨x,y⟩:=hz
  change z.1 ≡ 9 [ZMOD 16] at x
  change z.2 ≡ 0 [ZMOD 16] at y
  obtain ⟨a,ha⟩:=Int.modEq_iff_dvd.mp x.symm
  obtain ⟨b,hb⟩:=Int.modEq_iff_dvd.mp y.symm
  have ex : z.1=9+16*a := by linarith
  have ey : z.2=16*b := by linarith
  have order (n e : ℕ) (fac : ∃ k : ℤ,(n:ℤ)=(2:ℤ)^e*(2*k+1)) : padicValNat 2 n=e := by
    obtain ⟨k,hk⟩:=fac
    have cong : (n:ℤ) ≡ (2:ℤ)^e [ZMOD (2:ℤ)^(e+1)] := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨-k,?_⟩
      rw [hk,pow_succ]
      ring
    have got := (Sun28.ComparisonCRT.exact_order Nat.prime_two cong).2
    simpa only [padicValInt,Int.natAbs_natCast] using got
  constructor
  · apply order
    refine ⟨12+40*a+32*a^2+32*b^2,?_⟩
    rw [nat_norm,ex,ey]
    norm_num
    ring
  · apply order
    refine ⟨2*a+2*a^2+2*b^2,?_⟩
    rw [nat_norm,ex,ey]
    norm_num
    ring

end Sun28.GaussianSelection
#print axioms Sun28.GaussianSelection.ray_seven
#print axioms Sun28.GaussianSelection.ray_dyadic
