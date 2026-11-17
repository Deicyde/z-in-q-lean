import IntegralRay
import GaussianUnits
import Mathlib.RingTheory.Coprime.Lemmas

namespace Sun28.Reciprocity
open Sun28.RayDensity
noncomputable section

/-- Simultaneous reduction of the two integer coordinates. -/
def gaussianRed (m : ℕ) : GaussianInt →+* GR m where
  toFun z := ⟨z.re,z.im⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp [Zsqrtd.re_mul,Zsqrtd.im_mul]

theorem gaussianRed_surjective (m : ℕ) [NeZero m] : Function.Surjective (gaussianRed m) := by
  intro z
  refine ⟨⟨z.re.val,z.im.val⟩,?_⟩
  apply QuadraticAlgebra.ext <;> simp [gaussianRed]

theorem gaussianRed_kernel (m : ℕ) :
    RingHom.ker (gaussianRed m) = principal (m:GaussianInt) := by
  ext z
  change (gaussianRed m z = 0) ↔ z ∈ Ideal.span {(m:GaussianInt)}
  rw [Ideal.mem_span_singleton]
  constructor
  · intro h
    have hr : (z.re : ZMod m) = 0 := congrArg QuadraticAlgebra.re h
    have hi : (z.im : ZMod m) = 0 := congrArg QuadraticAlgebra.im h
    obtain ⟨a,ha⟩:= (ZMod.intCast_zmod_eq_zero_iff_dvd z.re m).1 hr
    obtain ⟨b,hb⟩:= (ZMod.intCast_zmod_eq_zero_iff_dvd z.im m).1 hi
    refine ⟨⟨a,b⟩,?_⟩
    apply Zsqrtd.ext <;> simp [ha,hb]
  · rintro ⟨t,rfl⟩
    rw [map_mul,map_natCast]
    have h : (m:GR m)=0 := by ext <;> simp
    rw [h,zero_mul]

def gaussianQuotient (m:ℕ) [NeZero m] :
    GaussianInt ⧸ principal (m:GaussianInt) ≃+* GR m :=
  (Ideal.quotEquivOfEq (gaussianRed_kernel m).symm).trans
    ((gaussianRed m).quotientKerEquivOfSurjective (gaussianRed_surjective m))

@[simp] theorem gaussianQuotient_mk (m:ℕ) [NeZero m] (x:GaussianInt) :
    gaussianQuotient m (residue (principal (m:GaussianInt)) x)=gaussianRed m x := rfl

variable {I:Type*} [Fintype I] (m:I→ℕ)
abbrev piece (i:I) := principal (m i:GaussianInt)
abbrev modulus := ⨅ i,piece m i

omit [Fintype I] in
theorem ideals_coprime (cop:Pairwise (Function.onFun Nat.Coprime m)) :
    Pairwise (Function.onFun IsCoprime (piece m)) := by
  intro i j ne
  apply (Ideal.isCoprime_span_singleton_iff _ _).2
  simpa using (cop ne).isCoprime.map (Int.castRingHom GaussianInt)

/-- Actual Chinese remainder ring, including arbitrary dyadic or prime-power factors. -/
def gaussianCRT [∀i,NeZero (m i)] (cop:Pairwise (Function.onFun Nat.Coprime m)) :
    GaussianInt ⧸ modulus m ≃+* ∀ i,GR (m i) :=
  (Ideal.quotientInfRingEquivPiQuotient _ (ideals_coprime m cop)).trans
    (RingEquiv.piCongrRight (fun i=>gaussianQuotient (m i)))

@[simp] theorem gaussianCRT_mk [∀i,NeZero (m i)] (cop:Pairwise (Function.onFun Nat.Coprime m))
    (z:GaussianInt) (i:I) :
    gaussianCRT m cop (residue (modulus m) z) i = gaussianRed (m i) z := rfl

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.gaussianRed_kernel
#print axioms Sun28.Reciprocity.gaussianQuotient
#print axioms Sun28.Reciprocity.gaussianCRT
#print axioms Sun28.Reciprocity.gaussianCRT_mk
