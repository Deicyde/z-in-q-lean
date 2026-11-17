import OrdinaryTransfer
import WindowGeometry

namespace Sun28.PrimeTransfer
open Finset Filter Topology Sun28.PrimeMass Sun28.SinglePrime
open scoped Classical
noncomputable section

/-- One bounded model for an ordinary prime-dominated function on an interior
cyclic interval. The little-o replacement estimates are expressed at accuracy ε
after fixing an auxiliary primorial, before the row number or asymptotic scale. -/
def InteriorModel : Prop :=
  ∀ (c : Finset ℤ) (d : ℕ), 0<d → 0∈c → ∃ C : ℝ, 0<C ∧
    ∀ (η : ℝ), 0<η → ∀ (ε : ℝ), 0<ε → ∃ V : ℕ, 0<V ∧
    ∀ j : ℕ, ∀ᶠ t : ℕ in atTop,
      let N:=lengthAt t
      let W:=rowWidth j N
      let n:=N/V
      let M:=W/(V*d)
      ∃ hn : 0<n, letI : NeZero n := ⟨hn.ne'⟩
        ∀ b∈units V, ∀ f : ZMod n→ℝ,
        (∀ x, 0≤f x ∧ f x ≤ (V.totient:ℝ)/V*(if (b+V*x.val).Prime then Real.log (b+V*x.val:ℕ) else 0)) →
        η*n ≤ ∑ x,f x → ∃ g : ZMod n→ℝ, (∀ x,0≤g x ∧ g x≤C) ∧ (η/2)*n ≤ ∑ x,g x ∧
        ∀ D⊆c, ∀ h∈c, h∉D →
          singleError c D h f g ((V*d^2:ℕ):ZMod n) M ≤ ε*((n:ℝ)*M)

private theorem eventual_steps (j A : ℕ) : ∀ᶠ t : ℕ in atTop, A ≤ rowWidth j (lengthAt t) := by
  exact length_grows.eventually (row_grows j A)

private theorem row_is_narrow (c : Finset ℤ) :
    ∃ I : ℕ, ∀ j≥I, ∀ N : ℕ, ∀ h∈c, 8*h.natAbs*(rowWidth j N)^2 ≤ N := by
  let I:=8*c.sup Int.natAbs
  refine ⟨I,fun j hj N h hm => ?_⟩
  have hh : h.natAbs ≤ c.sup Int.natAbs := le_sup (f:=Int.natAbs) hm
  have small : 8*h.natAbs ≤ (j+1)^2 := by dsimp [I] at hj; nlinarith only [hh,hj,Nat.zero_le j,Nat.zero_le (j^2)]
  have floor := Nat.div_mul_le_self (Nat.sqrt N) (j+1)
  have up := Nat.pow_le_pow_left floor 2
  have sq : N.sqrt^2 ≤ N := Nat.sqrt_le' N
  calc
    _ ≤ (j+1)^2 * (rowWidth j N)^2 := Nat.mul_le_mul_right _ small
    _ = ((N.sqrt/(j+1))*(j+1))^2 := by unfold rowWidth; ring
    _ ≤ N.sqrt^2 := up
    _ ≤ N := sq

theorem model_geometry (interior : InteriorModel) : OrdinaryModelInputs := by
  intro c d dp zero
  obtain ⟨C,cp,models⟩ := interior c d dp zero
  refine ⟨C,cp,fun η ep ε epos B => ?_⟩
  obtain ⟨V,vp,run⟩ := models η ep ε epos
  obtain ⟨I,narrow⟩ := row_is_narrow c
  refine ⟨V,vp,I,fun j jI => ?_⟩
  filter_upwards [run j,length_grows.eventually (eventually_ge_atTop (2*V)),
    eventual_steps j ((2*B+2)*(V*d))] with t h space steps
  obtain ⟨hn,model⟩:=h
  obtain ⟨_,width,wide,short,volume⟩ := window_geometry c vp dp space steps (narrow j jI _)
  exact ⟨hn,_,width,wide,short,volume,model⟩

theorem hybrid_of_interior (grid : PublishedRecurrence) (onePrime : OnePrimeDensity)
    (interior : InteriorModel) (upper : RelativeUpperInputs) : HybridInputs :=
  hybrid_of_ordinary grid onePrime (model_geometry interior) upper

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.model_geometry
#print axioms Sun28.PrimeTransfer.hybrid_of_interior
