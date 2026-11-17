import GaussianWindow

namespace Sun28.PrimeModel
open Sun28.Reciprocity Sun28.PrimeValues Sun28.PrimeTransfer
open Sun28.RayDensity Sun28.RayDensity.Artin
noncomputable section

private theorem divides_rational_prime {z : GaussianInt} (hz : Prime z) (m : ℕ)
    (hm : m ≠ 0) (div : z ∣ (m:GaussianInt)) : ∃ p : ℕ, p.Prime ∧ z ∣ (p:GaussianInt) := by
  have aux : ∀ n : ℕ, n ≠ 0 → z ∣ (n:GaussianInt) →
      ∃ p : ℕ, p.Prime ∧ z ∣ (p:GaussianInt) := by
    apply Nat.recOnMul
    · simp
    · intro _ one
      exact (hz.not_isUnit (isUnit_of_dvd_one (by simpa using one))).elim
    · intro p prime _ d
      exact ⟨p,prime,d⟩
    · intro a b ihA ihB ne mul
      rw [Nat.cast_mul] at mul
      rcases hz.dvd_or_dvd mul with e|e
      · exact ihA (left_ne_zero_of_mul ne) e
      · exact ihB (right_ne_zero_of_mul ne) e
  exact aux m hm div

private theorem unit_axis (z : GaussianInt) (p : ℕ) (u : GaussianIntˣ)
    (e : (p:GaussianInt)=z*(u:GaussianInt)) : z.re=0 ∨ z.im=0 := by
  have h : z=(p:GaussianInt)*(↑(u⁻¹):GaussianInt) := by rw [e]; simp [mul_assoc]
  obtain ⟨j,uj⟩ := global_units u
  rw [h,uj]
  fin_cases j <;> simp [quarter,imaginary,pow_succ]

/-- An off-axis Gaussian prime has prime rational norm. -/
theorem off_axis_prime {z : GaussianInt} (hz : Prime z) (re : z.re ≠ 0) (im : z.im ≠ 0) :
    z.norm.natAbs.Prime := by
  have zn : z.norm.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (GaussianInt.norm_pos.mpr hz.ne_zero).ne'
  have div : z ∣ (z.norm.natAbs:GaussianInt) := by
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  obtain ⟨p,hp,u,he⟩ := divides_rational_prime hz _ zn div
  have un : ¬ IsUnit u := by
    rintro ⟨v,rfl⟩
    exact (unit_axis z p v he).elim re im
  have en := congrArg (fun x:GaussianInt => x.norm.natAbs) he
  simp only [Zsqrtd.norm_natCast, Int.natAbs_natCast,
    Zsqrtd.norm_mul, Int.natAbs_mul] at en
  have exactNorm := (hp.mul_eq_prime_sq_iff (mt Zsqrtd.norm_eq_one_iff.mp hz.not_isUnit)
    (mt Zsqrtd.norm_eq_one_iff.mp un)).mp (by simpa only [pow_two] using en.symm)
  exact exactNorm.1 ▸ hp

/-- Every prime ideal in the chosen fixed ray already has prime rational norm.
The two nonzero coordinates modulo seven exclude all inert rational ideals. -/
theorem fixed_ideal_prime_norm {K : ℕ} (J : Ideals K) (jprime : J.val.IsPrime)
    (ray : word J = fixedWord K) : (norm J).Prime := by
  obtain ⟨z,dy,unit,gen,card,coord⟩ := prime_ideal_data (moduli K) (level_coprime K) J
  have good : admissible K (primeTuple (moduli K) z.re z.im dy unit) := by
    rw [←coord]
    change admissible K (word J)
    rw [ray]
    exact fixed_admissible K
  have sevenCoord := ((admissible_generator K _ _ dy unit).1 good).2.1
  obtain ⟨a,b⟩ := sevenCoord
  have re : z.re ≠ 0 := by
    intro zero
    rw [zero] at a
    exact (by decide : ¬ (0:ℤ) ≡ 1 [ZMOD 7]) a
  have im : z.im ≠ 0 := by
    intro zero
    rw [zero] at b
    exact (by decide : ¬ (0:ℤ) ≡ 3 [ZMOD 7]) b
  have nonzero : z ≠ 0 := fun h => re (h ▸ rfl)
  have principalPrime : (Ideal.span {z}).IsPrime := by
    change (principal z).IsPrime
    rw [gen]
    exact jprime
  have prime := (Ideal.span_singleton_prime nonzero).mp principalPrime
  rw [show norm J=z.norm.natAbs from card]
  exact off_axis_prime prime re im

def FixedIdeal (K : ℕ) := {J : Ideals K // J.val.IsPrime ∧ word J=fixedWord K}

/-- The absolute norm is a bijection on all prime ideals in this ray, including at small norms. -/
def fixed_prime_equiv (K : ℕ) : FixedIdeal K ≃ {p : ℕ // oneClass K p} := by
  let normMap (J : FixedIdeal K) : {p : ℕ // oneClass K p} :=
    ⟨norm J.val,fixed_ideal_prime_norm _ J.2.1 J.2.2,J.val,rfl,J.2.2⟩
  apply Equiv.ofBijective normMap
  constructor
  · intro I J h
    have eq : norm I.val=norm J.val := congrArg Subtype.val h
    have uniq := oriented_subsingleton (L:=K) (fixed_ideal_prime_norm _ I.2.1 I.2.2)
    let U : Oriented K (norm I.val) := ⟨I.val,rfl,by rw [I.2.2]; exact fixed_admissible K⟩
    let V : Oriented K (norm I.val) := ⟨J.val,eq.symm,by rw [J.2.2]; exact fixed_admissible K⟩
    exact Subtype.ext (congrArg (fun t : Oriented K (norm I.val) => t.val) (uniq.allEq U V))
  · rintro ⟨p,prime,J,card,ray⟩
    exact ⟨⟨J,prime_ideal_of_card (moduli K) (level_coprime K) prime J card,ray⟩,Subtype.ext card⟩

@[simp] theorem fixed_prime_value {K : ℕ} (J : FixedIdeal K) :
    ((fixed_prime_equiv K J):ℕ) = norm J.val := rfl

end
end Sun28.PrimeModel
#print axioms Sun28.PrimeModel.off_axis_prime
#print axioms Sun28.PrimeModel.fixed_ideal_prime_norm
#print axioms Sun28.PrimeModel.fixed_prime_equiv
#print axioms Sun28.PrimeModel.fixed_prime_value
