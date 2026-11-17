import HeightTransport

/-! Projective normalization at arbitrary integer representatives; zero coordinates
and zero contact forms are valued at infinity. -/
namespace Sun28.Ordinary

def integerOrder (p : ℕ) (x : ℤ) : WithTop ℕ :=
  if x=0 then ⊤ else (padicValInt p x:WithTop ℕ)

private theorem layer_iff (p : ℕ) [Fact p.Prime] (d : ℕ) (x : ℤ) :
    (d:WithTop ℕ) ≤ integerOrder p x ↔ (p:ℤ)^d ∣ x := by
  rw [padicValInt_dvd_iff]
  by_cases e:x=0 <;> simp [integerOrder,e]

/-- The minimum of both coordinate orders is unchanged, even if a coordinate vanishes. -/
theorem minimum_order_phi (p : ℕ) [Fact p.Prime] (U V : ℤ) :
    min (integerOrder p (2*U+V)) (integerOrder p U)=min (integerOrder p U) (integerOrder p V) := by
  have layers (d:ℕ) : (d:WithTop ℕ) ≤ min (integerOrder p (2*U+V)) (integerOrder p U) ↔
      (d:WithTop ℕ) ≤ min (integerOrder p U) (integerOrder p V) := by
    simp only [le_min_iff,layer_iff]
    constructor
    · rintro ⟨sum,u⟩
      exact ⟨u,by simpa using dvd_sub sum (dvd_mul_of_dvd_right u 2)⟩
    · rintro ⟨u,v⟩
      exact ⟨dvd_add (dvd_mul_of_dvd_right u 2) v,u⟩
  have eq_of_layers (a b : WithTop ℕ) (h : ∀ d : ℕ, (d:WithTop ℕ) ≤ a ↔ (d:WithTop ℕ) ≤ b) : a=b := by
    induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe
    case top.top => rfl
    case top.coe n =>
      have e : n+1 ≤ n := WithTop.coe_le_coe.mp ((h (n+1)).mp le_top)
      omega
    case coe.top m =>
      have e : m+1 ≤ m := WithTop.coe_le_coe.mp ((h (m+1)).mpr le_top)
      omega
    case coe.coe m n =>
      exact le_antisymm ((h m).mp le_rfl) ((h n).mpr le_rfl)
  exact eq_of_layers _ _ layers

/-- Normalized projective depth for a homogeneous primitive defining form. -/
def normalizedDepth (p : ℕ) (value U V : ℤ) : WithTop ℕ :=
  integerOrder p value - min (integerOrder p U) (integerOrder p V)

theorem normalized_depth_pullback (p : ℕ) [Fact p.Prime] (i : Fin 5) (U V : ℤ) :
    normalizedDepth p (oldForm i (2*U+V) U) (2*U+V) U=normalizedDepth p (pulledForm i U V) U V := by
  unfold normalizedDepth
  rw [old_form_pullback,minimum_order_phi]
  split_ifs <;> simp [integerOrder,padicValInt]

end Sun28.Ordinary
#print axioms Sun28.Ordinary.minimum_order_phi
#print axioms Sun28.Ordinary.normalized_depth_pullback
