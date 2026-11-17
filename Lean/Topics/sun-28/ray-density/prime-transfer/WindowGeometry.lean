import TransferRows

namespace Sun28.PrimeTransfer
open Finset
open scoped Classical
noncomputable section

/-- Floor division in both coordinates costs at most a factor four.
The signed shifts unwrap on every fixed row past an explicit coefficient bound. -/
theorem window_geometry (c : Finset ℤ) {N W V d B : ℕ} (vp : 0<V) (dp : 0<d)
    (space : 2*V ≤ N) (steps : (2*B+2)*(V*d) ≤ W)
    (narrow : ∀ h∈c, 8*h.natAbs*W^2 ≤ N) :
    let n:=N/V
    let M:=W/(V*d)
    0<n ∧ V*d*M ≤ W ∧ 2*B ≤ M ∧
      (∀ h∈c,4*(V*d^2*h.natAbs*M^2) ≤ n) ∧ N*W ≤ 4*V^2*d*(n*M) := by
  dsimp only
  let n:=N/V
  let M:=W/(V*d)
  have vd : 0<V*d := Nat.mul_pos vp dp
  have hn : 0<n := Nat.div_pos (by omega) vp
  have stepTwo : 2*(V*d) ≤ W :=
    (Nat.mul_le_mul_right (V*d) (by omega : 2≤2*B+2)).trans steps
  have floor (U Q : ℕ) (qpos : 0<Q) (big : 2*Q ≤ U) : U ≤ 2*(Q*(U/Q)) := by
    have := Nat.mod_add_div U Q
    have := Nat.mod_lt U qpos
    omega
  have cap : V*d*M ≤ W := Nat.mul_div_le W (V*d)
  have many : 2*B ≤ M := (Nat.le_div_iff_mul_le vd).mpr
    ((Nat.mul_le_mul_right (V*d) (by omega : 2*B≤2*B+2)).trans steps)
  have nearN := floor N V vp space
  have nearW := floor W (V*d) vd stepTwo
  refine ⟨hn,cap,many,?_,?_⟩
  · intro h hh
    apply Nat.le_of_mul_le_mul_left (c:=2*V) _ (by positivity)
    have pstep : (V*d*M)^2 ≤ W^2 := Nat.pow_le_pow_left cap 2
    calc
      _ = 8*h.natAbs*(V*d*M)^2 := by ring
      _ ≤ 8*h.natAbs*W^2 := Nat.mul_le_mul_left _ pstep
      _ ≤ N := narrow h hh
      _ ≤ 2*V*(N/V) := by simpa only [mul_assoc] using nearN
  · calc
      _ ≤ (2*(V*n))*(2*((V*d)*M)) := Nat.mul_le_mul nearN nearW
      _ = _ := by dsimp [n,M]; ring

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.window_geometry
