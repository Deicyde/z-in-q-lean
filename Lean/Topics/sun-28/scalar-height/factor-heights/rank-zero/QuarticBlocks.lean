import EllipticDescent

namespace Sun28.ScalarRankZero
open Sun28.FactorHeights
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

/-- Integral primitive points include the point at infinity whenever its leading class is a square. -/
def represented (A B e : ℤ) : Prop :=
  ∃ u v z : ℤ, u.natAbs.Coprime v.natAbs ∧ z^2 = quartic e A (B/e) u v

private def blocked (p n : ℕ) [NeZero n] (h : p∣n) (e A c : ℤ) : Prop :=
  ∀ u∈squares n, ∀v∈squares n,
    ¬(ZMod.castHom h (ZMod p) u=0 ∧ ZMod.castHom h (ZMod p) v=0) →
    (e:ZMod n)*u^2+(A:ZMod n)*u*v+(c:ZMod n)*v^2∉squares n

private instance (p n : ℕ) [NeZero n] (h:p∣n) (e A c:ℤ) :
    Decidable (blocked p n h e A c) := by unfold blocked; infer_instance

private theorem exclude {p n : ℕ} [NeZero n] (pp:p.Prime) (h:p∣n) {A B e : ℤ}
    (localBlock:blocked p n h e A (B/e)) : ¬represented A B e := by
  rintro ⟨u,v,z,cop,eq⟩
  let : Fact p.Prime := ⟨pp⟩
  have mem (a:ℤ):(a:ZMod n)^2∈squares n := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have prim:¬(ZMod.castHom h (ZMod p) ((u:ZMod n)^2)=0 ∧
      ZMod.castHom h (ZMod p) ((v:ZMod n)^2)=0) := by
    rintro ⟨a,b⟩
    rw [map_pow,map_intCast] at a b
    have up:=(ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp (sq_eq_zero_iff.mp a)
    have vp:=(ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp (sq_eq_zero_iff.mp b)
    exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt (by simpa using Int.natAbs_dvd_natAbs.mpr up)
      (by simpa using Int.natAbs_dvd_natAbs.mpr vp)) cop
  apply localBlock _ (mem u) _ (mem v) prim
  convert mem z using 1
  have eq' : (z:ZMod n)^2=quartic (e:ZMod n) (A:ZMod n) ((B/e:ℤ):ZMod n) (u:ZMod n) (v:ZMod n) := by
    simpa [quartic] using congrArg (Int.castRingHom (ZMod n)) eq
  rw [eq']; unfold quartic; ring

private theorem negative_quartic {A B e : ℤ} (a:A<0) (b:B/e<0) (s:e<0) : ¬represented A B e := by
  rintro ⟨u,v,z,cop,h⟩
  have nz : u≠0 ∨ v≠0 := by
    by_contra! zero
    obtain ⟨r,t⟩:=zero
    simp [r,t] at cop
  have mid : A*u^2*v^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg a.le (sq_nonneg u)) (sq_nonneg v)
  have un : 0≤u^4 := by positivity
  have vn : 0≤v^4 := by positivity
  unfold quartic at h
  rcases nz with uh|vh
  · have lt: e*u^4<0 := mul_neg_of_neg_of_pos s (lt_of_le_of_ne un (Ne.symm (pow_ne_zero 4 uh)))
    linarith [mul_nonpos_of_nonpos_of_nonneg b.le vn,sq_nonneg z]
  · have lt: (B/e)*v^4<0 := mul_neg_of_neg_of_pos b (lt_of_le_of_ne vn (Ne.symm (pow_ne_zero 4 vh)))
    linarith [mul_nonpos_of_nonpos_of_nonneg s.le un,sq_nonneg z]

private theorem previous (j:Fin 6) {A B e:ℤ} (h:descentRows j=(e,A,B/e)) :
    ¬represented A B e := by
  rintro ⟨u,v,z,cop,eq⟩
  apply six_quartic_obstructions j cop
  simpa [h] using eq

/-- All four non-image signed divisors on the direct models, without a squareclass-coset convention. -/
theorem direct_exclusions :
    (¬represented 10 24 2) ∧ (¬represented 10 24 (-2)) ∧
    (¬represented 10 24 3) ∧ (¬represented 10 24 (-3)) ∧
    (¬represented 503 28096 2) ∧ (¬represented 503 28096 (-2)) ∧
    (¬represented 503 28096 878) ∧ (¬represented 503 28096 (-878)) := by
  refine ⟨previous 0 (by decide), ?_, ?_, ?_, previous 2 (by decide), ?_, ?_, ?_⟩
  · exact exclude (p:=2) (n:=32) (by decide) (by decide) (by decide)
  · exact exclude (p:=2) (n:=64) (by decide) (by decide) (by decide)
  · exact exclude (p:=2) (n:=64) (by decide) (by decide) (by decide)
  · exact exclude (p:=5) (n:=5) (by decide) (by decide) (by decide)
  · exact exclude (p:=5) (n:=5) (by decide) (by decide) (by decide)
  · exact exclude (p:=5) (n:=5) (by decide) (by decide) (by decide)

/-- The real place removes every negative dual class; the four nontrivial positive ones fail locally. -/
theorem dual_exclusions :
    (∀e:ℤ, e<0 → 4/e<0 → ¬represented (-20) 4 e) ∧ (¬represented (-20) 4 2) ∧
    (∀e:ℤ, e<0 → 140625/e<0 → ¬represented (-1006) 140625 e) ∧
    (¬represented (-1006) 140625 3) ∧ (¬represented (-1006) 140625 5) ∧
    (¬represented (-1006) 140625 15) := by
  refine ⟨?_,previous 1 (by decide),?_,previous 3 (by decide),previous 4 (by decide),previous 5 (by decide)⟩
  · exact fun _ he hc => negative_quartic (by decide) hc he
  · exact fun _ he hc => negative_quartic (by decide) hc he

end Sun28.ScalarRankZero
#print axioms Sun28.ScalarRankZero.direct_exclusions
#print axioms Sun28.ScalarRankZero.dual_exclusions
