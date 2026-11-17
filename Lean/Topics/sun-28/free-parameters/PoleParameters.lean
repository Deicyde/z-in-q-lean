import ForwardSoundness

/-! The two continuously free pole parameters and the remaining finite choices. -/
namespace Sun28.Forward
open Sun28.Ordinary Sun28.ScalarHeight Sun28.WitnessIndices ZInQ
noncomputable section

def poleAt (U : Finset ℚ) (B e z : ℚ) : Prop :=
  B=0 ∨ ∃ μ ∈ U, poleBranch μ B e z

theorem pole_parameters (U : Finset ℚ) (B : ℚ) :
    polePredicate U B ↔ ∃ e z, poleAt U B e z := by
  constructor
  · rintro (h|⟨μ,hm,e,z,h⟩)
    · exact ⟨0,0,Or.inl h⟩
    · exact ⟨e,z,Or.inr ⟨μ,hm,h⟩⟩
  · rintro ⟨e,z,h|⟨μ,hm,h⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨μ,hm,e,z,h⟩

/-- For fixed pole parameters and multiplier, the two ordinates are among four signed choices. -/
theorem pole_root_choices (A e H z : ℚ) :
    ∃ L : Finset (ℚ × ℚ), L.card ≤ 4 ∧
      ∀ y u : ℚ, y^2=A*(A-e)*(A+3*e) → u^2=A*(A*z^2-e*H)*(A*z^2+3*e*H) → (y,u)∈L := by
  classical
  by_cases existsRoots : ∃ y u : ℚ, y^2=A*(A-e)*(A+3*e) ∧ u^2=A*(A*z^2-e*H)*(A*z^2+3*e*H)
  · obtain ⟨a,b,ea,eb⟩ := existsRoots
    refine ⟨{(a,b),(a,-b),(-a,b),(-a,-b)},?_,?_⟩
    · exact le_trans (Finset.card_insert_le ..) (by
        have h := Finset.card_insert_le (a,-b) {(-a,b),(-a,-b)}
        have j := Finset.card_insert_le (-a,b) {(-a,-b)}
        simp only [Finset.card_singleton] at j
        omega)
    · intro y u ey eu
      have aeq : y^2=a^2 := ey.trans ea.symm
      have beq : u^2=b^2 := eu.trans eb.symm
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp aeq) with h|h <;>
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp beq) with t|t <;> simp [h,t]
  · exact ⟨∅,by simp,fun y u hy hu => False.elim (existsRoots ⟨y,u,hy,hu⟩)⟩

def ordinaryTraceAt (w : NinePoints) (M : ℕ) (c : ℤ) (β A t : ℚ) : ℚ :=
  ordinaryTrace (detector A t) (fun i => ordinaryAt w M c β i /
    (algebraMap ℚ K0 (t-3))^(orderRequired i+1)) orderRequired

def ordinaryAtPair (w : NinePoints) (M : ℕ) (c : ℤ) (β A t : ℚ) (U : Finset ℚ) (e z : ℚ) : Prop :=
  let T := ordinaryTraceAt w M c β A t
  T≠0 ∧ poleAt U (detector A t/T^2) e z

theorem ordinary_parameters (w M c β A t U) :
    ordinaryAccepted w M c β A t U ↔ ∃ e z, ordinaryAtPair w M c β A t U e z := by
  unfold ordinaryAccepted ordinaryAtPair ordinaryTraceAt
  dsimp only
  rw [pole_parameters]
  exact ⟨fun ⟨t,⟨e,z,p⟩⟩ => ⟨e,z,t,p⟩,fun ⟨e,z,t,p⟩ => ⟨t,e,z,p⟩⟩

def scalarAtPair (w : NinePoints) (M : ℕ) (r Γ : ℚ) (D : ℕ) (U : Finset ℚ) (e z : ℚ) : Prop :=
  let T := scalarTree r (scalarEntries w M)
  ∃ δ : ℚ, (δ=1 ∨ δ= -1) ∧ T≠0 ∧ poleAt U (signedValue r δ Γ D T) e z

theorem scalar_parameters (w M r Γ D U) :
    scalarAccepted w M r Γ D U ↔ ∃ e z, scalarAtPair w M r Γ D U e z := by
  constructor
  · rintro ⟨δ,hd,ht,p⟩
    obtain ⟨e,z,p⟩ := (pole_parameters ..).1 p
    exact ⟨e,z,δ,hd,ht,p⟩
  · rintro ⟨e,z,δ,hd,ht,p⟩
    exact ⟨δ,hd,ht,(pole_parameters ..).2 ⟨e,z,p⟩⟩

end
end Sun28.Forward
#print axioms Sun28.Forward.pole_parameters
#print axioms Sun28.Forward.pole_root_choices
#print axioms Sun28.Forward.ordinary_parameters
#print axioms Sun28.Forward.scalar_parameters
