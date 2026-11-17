import IntegralTruncation

/-! Local integrality of all sixteen expressions at each prime element over a fixed prime. -/
namespace Sun28.OrdinaryIntegrality
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.Ordinary Sun28.ScalarTrace Sun28.FixedPreparation Sun28.Forward Sun28.WitnessIndices
noncomputable section
attribute [local irreducible] anchor paperGenerator
set_option maxHeartbeats 70000

theorem lucas_integral (v : AddValuation K0 (WithTop ℤ)) {x y z : K0}
    (hx : Vge v 0 x) (hy : Vge v 0 y) (hz : Vge v 0 z) : Vge v 0 (lucas x y z) := by
  have two:=vge_ofNat (v:=v) 2
  have one : Vge v 0 (1:K0) := by simp [Vge]
  have d:=hx.sub two
  have mul {u w : K0} (a : Vge v 0 u) (b : Vge v 0 w) : Vge v 0 (u*w) := a.mul b
  have ans:=((mul hy hy).sub (mul (mul (mul hx d) hy) hz)).add (mul (mul d d) (mul hz hz))
  simpa only [lucas,pow_two] using ans.sub one

theorem multiples_of_anchor {q : ℕ} [Fact q.Prime] (small : q≤23) {π : Zs}
    (prime : Prime π) (above : π∣(q:Zs)) (b : K0) (bi : Vge (vP π prime) 0 b)
    (P : (curve b).Point) (c j n : ℤ) (anchorNear : c • P∈W1 (vP π prime) b) (mul : c∣j) :
    Vge (vP π prime) 0 (reciprocal ((j*n) • P)) ∧
    Vge (vP π prime) 0 (ordinaryRatio P (j*n) j) := by
  have near : j • P∈W1 (vP π prime) b := by
    obtain ⟨l,e⟩:=mul
    have member:=zsmul_mem_W1 (v:=vP π prime) (A:=b) bi (P:=c • P) anchorNear l
    have eq : j=l*c := e.trans (mul_comm _ _)
    rw [eq,mul_smul]
    exact member.1
  have bounds:=multiple_integral (b:=b) (Q:=j • P) small prime above bi near n
  have eq : (j*n) • P=n • (j • P) := by rw [mul_comm j n,mul_smul]
  rw [ordinaryRatio,eq]
  exact bounds

end
#print axioms multiples_of_anchor
#print axioms lucas_integral
end Sun28.OrdinaryIntegrality
