import ContactFactors
import FinitePoleValuations

namespace Sun28.ContactFactors
open Sun28.Ordinary Sun28.FixedPreparation Sun28.PreparedPoles
noncomputable section

/-- The five linear prime values give the requisite square reduced denominator.
Only an upper bound on the trace orders there and the depth at the fixed nine remain local inputs. -/
theorem prepared_detector {A : Fin 3→ℚ} {u v : ℕ} (h : PrimeValues A u v) (one : A 0=1) (vp : 0<v)
    (j : Fin 3) (nz : A j≠0) {T : ℚ} (T0 : T≠0)
    (exclude : ∀ p∈selected h j, ¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0)
    (traceOrder : ∀ p∈selected h j, padicValRat p T≤0)
    (interval : let R:=detector (A j) (argument A u v j); 0<R/T^2 ∧ R/T^2<1/2)
    (depth : ∀ p∈primes, 4≤padicValRat p (detector (A j) (argument A u v j)/T^2)) :
    Prepared (detector (A j) (argument A u v j)/T^2) := by
  let s:=selected h j
  have first (p : ℕ) (hp : p∈s) :=
    selected_unit h one vp nz hp (exclude p hp).1 (exclude p hp).2.1 (exclude p hp).2.2
  have mem : h.value (-0/A j)∈s :=
    Finset.mem_image.mpr ⟨0,(by norm_num [marks]),rfl⟩
  have w0 : ((dilation A*v:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos (dilation_positive A) vp).ne'
  have f0 : scaleFactor (dilation A*v) (argument A u v j)≠0 :=
    div_ne_zero one_ne_zero (mul_ne_zero (pow_ne_zero 5 w0) (pow_ne_zero 3 (sub_ne_zero.mpr (first _ mem).1)))
  refine ⟨FinitePole.ordinary_square_den s (fun _ hp => selected_prime h hp) f0 T0
    (detector_factorization h vp j nz) (fun p hp => ?_),interval.1,interval.2,depth⟩
  rw [(first p hp).2]
  exact traceOrder p hp

end
end Sun28.ContactFactors
#print axioms Sun28.ContactFactors.prepared_detector
