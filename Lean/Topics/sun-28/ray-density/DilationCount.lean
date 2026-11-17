import NumericalPattern

namespace Sun28.RayDensity
open Finset Sun28.FinitePattern Sun28.ContactFactors
noncomputable section
open scoped Classical

/-- Replacing w by d v preserves all shifts and handles the floors in the companion's short box. -/
theorem dilation_identity (A : Fin 3→ℚ) {d : ℕ} (dp : 0<d) (L N W : ℕ) :
    patternMass A d L L N W =
      ∑ w ∈ Ioc (N/2) N ×ˢ Icc 1 (W/d),
        ∏ i : ↥(shifts A),primeWeight L L
          ((w.1:ℤ)+(offset (dilation A) i*(d:ℤ)^2)*(w.2:ℤ)^2) := by
  let src:=Ioc (N/2) N ×ˢ Icc 1 (W/d)
  let tgt:=(Ioc (N/2) N ×ˢ Icc 1 W).filter (fun z : ℕ×ℕ=>d∣z.2)
  let f := fun z : ℕ×ℕ => (z.1,d*z.2)
  have inj : Function.Injective f := by
    rintro ⟨u,w⟩ ⟨v,h⟩ e
    have pair : (u,d*w)=(v,d*h) := e
    have first : u=v := congrArg Prod.fst pair
    have last : d*w=d*h := congrArg Prod.snd pair
    exact Prod.ext first (Nat.eq_of_mul_eq_mul_left dp last)
  have image : src.image f=tgt := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨u,w⟩,mem,rfl⟩:=mem_image.mp hz
      obtain ⟨hu,hw⟩:=mem_product.mp mem
      obtain ⟨one,le⟩:=mem_Icc.mp hw
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨hu,mem_Icc.mpr ⟨Nat.mul_pos dp one,?_⟩⟩,dvd_mul_right _ _⟩
      simpa [mul_comm] using (Nat.le_div_iff_mul_le dp).mp le
    · intro hz
      obtain ⟨m,dw⟩:=mem_filter.mp hz
      obtain ⟨c,hc⟩:=dw
      obtain ⟨hu,hw⟩:=mem_product.mp m
      obtain ⟨one,le⟩:=mem_Icc.mp hw
      refine mem_image.mpr ⟨(z.1,c),mem_product.mpr ⟨hu,mem_Icc.mpr ⟨?_,?_⟩⟩,Prod.ext rfl hc.symm⟩
      · by_contra! hc0
        have : c=0 := by omega
        simp [this] at hc
        omega
      · apply (Nat.le_div_iff_mul_le dp).mpr
        simpa [mul_comm] using hc ▸ le
  change ∑ z∈tgt,patternWeight A L L z=_
  rw [←image,sum_image inj.injOn]
  apply sum_congr rfl
  intro q _
  apply prod_congr rfl
  intro i _
  congr 1
  dsimp [form,f]
  ring

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.dilation_identity
