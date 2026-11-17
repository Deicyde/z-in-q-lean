import PhysicalFactors

namespace Sun28.ConicSelection
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unnecessarySimpa false

private def screen (p n:ℕ) [NeZero n] (pn:p∣n) (S:Finset ℕ) : Finset ℕ :=
  let sq : Finset (ZMod n):=Finset.univ.image (fun z:ZMod n=>z^2)
  let rows:=(sq ×ˢ sq).filter fun t=>
    (ZMod.castHom pn (ZMod p) t.1 ≠ 0 ∨ ZMod.castHom pn (ZMod p) t.2 ≠ 0) ∧
    (p≠7 ∨ ZMod.castHom pn (ZMod p) t.2 ≠ 0) ∧
    7*(t.1-4*t.2)∈sq ∧ 16*t.1-15*t.2∈sq
  S.filter fun d=>∃t∈rows,∃w∈sq ×ˢ sq,
    (((7194:ℕ)/d:ℕ):ZMod n)*w.2-(d:ZMod n)*w.1=686*t.1-349*t.2 ∧ w.1*w.2=t.2^2

private theorem visible {s:ℚ} (f:Factors s) {d:ℕ} {u v:ℤ}
    (P:f.P=(d:ℤ)*u^2) (Q:f.Q=(((7194:ℕ)/d:ℕ):ℤ)*v^2) (uv:u*v=f.b^2)
    (p n:ℕ) [NeZero n] (hp:p.Prime) (pn:p∣n) {S:Finset ℕ} (ds:d∈S) : d∈screen p n pn S := by
  let _:Fact p.Prime:=⟨hp⟩
  let sqs:=Finset.univ.image (fun z:ZMod n=>z^2)
  have sqr (r:ℤ):(r:ZMod n)^2∈sqs := Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  have red (r:ℤ) (zr:ZMod.castHom pn (ZMod p) ((r:ZMod n)^2)=0) : (p:ℤ)∣r := by
    rw [map_pow,map_intCast] at zr
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd r p).mp (sq_eq_zero_iff.mp zr)
  apply Finset.mem_filter.mpr
  refine ⟨ds,⟨(f.a:ZMod n)^2,(f.b:ZMod n)^2⟩,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨sqr _,sqr _⟩,?_,?_,?_,?_⟩,
    ⟨(u:ZMod n)^2,(v:ZMod n)^2⟩,Finset.mem_product.mpr ⟨sqr _,sqr _⟩,?_,?_⟩
  · by_contra! h
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
      (by simpa using Int.natAbs_dvd_natAbs.mpr (red _ h.1))
      (by simpa using Int.natAbs_dvd_natAbs.mpr (red _ h.2))) f.cop
  · by_cases h:p=7
    · subst p; exact Or.inr (fun z=>f.odd7 (red _ z))
    · exact Or.inl h
  · convert sqr f.A7 using 1
    simpa using congrArg (Int.castRingHom (ZMod n)) f.mark7
  · convert sqr f.A16 using 1
    simpa using congrArg (Int.castRingHom (ZMod n)) f.mark16
  · let k:ℕ:=7194/d
    change (k:ZMod n)*_-(d:ZMod n)*_=_
    change f.Q=(k:ℤ)*v^2 at Q
    have e:=f.diff; rw [P,Q] at e
    simpa using congrArg (Int.castRingHom (ZMod n)) e
  · have e:u^2*v^2=(f.b^2)^2:=by rw [←mul_pow,uv]
    simpa using congrArg (Int.castRingHom (ZMod n)) e

private theorem at_eight : screen 2 8 (by decide) (7194:ℕ).divisors={2,3,11,66} := by decide
private theorem at_seven : screen 7 7 (by decide) {2,3,11,66}={3,66} := by decide

theorem at_two_seven {s:ℚ} (f:Factors s) {d:ℕ} (ds:d∈(7194:ℕ).divisors) {u v:ℤ}
    (P:f.P=(d:ℤ)*u^2) (Q:f.Q=(((7194:ℕ)/d:ℕ):ℤ)*v^2) (uv:u*v=f.b^2) : d=3 ∨ d=66 := by
  have m:=visible f P Q uv 2 8 (by decide) (by decide) ds
  rw [at_eight] at m
  have n:=visible f P Q uv 7 7 (by decide) (by decide) m
  simpa [at_seven] using n

end Sun28.ConicSelection
#print axioms Sun28.ConicSelection.at_two_seven