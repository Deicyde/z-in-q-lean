import IntegralAbscissa

namespace Sun28.PointLifts
open Sun28.PairedClasses ZInQ.RouteK
noncomputable section

def AnisotropicPrime (b p : ℕ) : Prop :=
  ¬IsSquare (b:ZMod p) ∧ ¬IsSquare (-3*(b:ZMod p))

private theorem anisotropic {p : ℕ} [Fact p.Prime] {a x y : ZMod p} (ns : ¬IsSquare a)
    (prim : x≠0 ∨ y≠0) : x^2-a*y^2≠0 := by
  intro e
  by_cases yn : y=0
  · have xn:=prim.resolve_right (not_not_intro yn)
    rw [yn] at e
    have xx : x^2=0:=by simpa using e
    exact pow_ne_zero 2 xn xx
  · apply ns
    refine ⟨x/y,?_⟩
    field_simp;linear_combination -e

/-- Both quadratic forms giving z are anisotropic, so its rational value is a p-adic unit. -/
theorem conic_anisotropic_unit {b p : ℕ} [Fact p.Prime] {z h : ℚ} (bp : 0<b)
    (bad : AnisotropicPrime b p) (E : (z-1)*(z+3)=(b:ℚ)*h^2) : padicValRat p z=0 := by
  obtain ⟨x,y,prim,eq⟩:=integral_abscissa bp E
  let X : ℤ:=x^2+3*(b:ℤ)*y^2
  let Y : ℤ:=x^2-b*y^2
  have num : (X:ZMod p)≠0:=by
    simpa [X,sub_neg_eq_add] using (anisotropic bad.2 (primitive_mod prim))
  have den : (Y:ZMod p)≠0:=by simpa [Y] using (anisotropic bad.1 (primitive_mod prim))
  have rep : Residue p z ((X:ZMod p)/Y):=by
    refine ⟨X,Y,den,?_,(div_mul_cancel₀ _ den).symm⟩
    simpa [abscissa,X,Y] using eq
  exact order_zero_of_residue rep (div_ne_zero num den)

theorem ratio_order {b p : ℕ} [Fact p.Prime] {θ s z h j : ℚ} (bp : 0<b)
    (tn : θ≠0) (bad : AnisotropicPrime b p) (F : ConicFibre b θ s z h j) :
    2*padicValRat p s=padicValRat p θ := by
  have H:=conic_anisotropic_unit bp bad F.first
  have J:=conic_anisotropic_unit bp bad F.second
  rw [padicValRat.mul (div_ne_zero (pow_ne_zero _ F.s_ne) tn) F.z_ne,
    padicValRat.div (pow_ne_zero _ F.s_ne) tn,padicValRat.pow,H] at J
  omega

theorem admissible_ratio_unit {b θ p : ℕ} [hp : Fact p.Prime] {s z h j : ℚ}
    (a : AdmissiblePair b θ) (bad : AnisotropicPrime b p) (F : ConicFibre b θ s z h j) :
    padicValRat p s=0 := by
  obtain ⟨bp,tp,_,_,_,_,_,_,_,bt,_⟩:=a
  have nt : ¬p∣θ:=by
    intro pt
    obtain ⟨w,e⟩:=bt p hp.out pt 1
    rw [pow_one] at e
    have E:=(ZMod.intCast_eq_intCast_iff _ _ p).mpr e
    exact bad.1 ⟨(w:ZMod p),by simpa [sq] using E.symm⟩
  have D:=ratio_order bp (by exact_mod_cast tp.ne') bad F
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nt] at D
  omega

/-- A prime exactly dividing b leaves only the reductions 1 and -3 for z. -/
theorem conic_ramified_ray {b p : ℕ} [hp : Fact p.Prime] {z h : ℚ}
    (bp : 0<b) (sf : Squarefree b) (pb : p∣b)
    (E : (z-1)*(z+3)=(b:ℚ)*h^2) : Residue p z 1 ∨ Residue p z (-3) := by
  obtain ⟨x,y,prim,eq⟩:=integral_abscissa bp E
  have bz: (b:ZMod p)=0:=(ZMod.natCast_eq_zero_iff b p).mpr pb
  by_cases xz : (x:ZMod p)=0
  · have yn:=(primitive_mod prim).resolve_left (not_not_intro xz)
    obtain ⟨a,xa⟩:=(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp xz
    obtain ⟨c,bc⟩:=pb
    have cn : (c:ZMod p)≠0:=by
      intro ce
      obtain ⟨e,ec⟩:=(ZMod.natCast_eq_zero_iff c p).mp ce
      apply Nat.squarefree_iff_prime_squarefree.mp sf p hp.out
      exact ⟨e,by rw [bc,ec];ring⟩
    have pn : (p:ℚ)≠0:=by exact_mod_cast hp.out.ne_zero
    let N : ℤ:=p*a^2+3*(c:ℤ)*y^2
    let D : ℤ:=p*a^2-c*y^2
    right
    refine ⟨N,D,?_,?_,?_⟩
    · simp [D,cn,yn]
    · rw [eq,xa,bc];unfold abscissa;dsimp [N,D];push_cast
      rw [show ((p:ℚ)*a)^2+3*(p*c)*y^2=(p*a^2+3*c*y^2)*p by ring,
        show ((p:ℚ)*a)^2-(p*c)*y^2=(p*a^2-c*y^2)*p by ring,
        mul_div_mul_right _ _ pn]
    · simp [N,D];ring
  · left
    refine ⟨x^2+3*(b:ℤ)*y^2,x^2-(b:ℤ)*y^2,?_,?_,?_⟩
    · simpa [bz] using pow_ne_zero 2 xz
    · simpa [abscissa] using eq
    · simp [bz]

/-- Explicit allowed values for the square ratio, without choosing a square root of θ. -/
def RamifiedRay (p θ : ℕ) [Fact p.Prime] (s : ℚ) : Prop :=
  Residue p (s^2) (θ:ZMod p) ∨ Residue p (s^2) ((-3:ZMod p)*(θ:ZMod p)) ∨ Residue p (s^2) (-(θ:ZMod p)/(3:ZMod p))

theorem ratio_ramified_ray {b θ p : ℕ} [hp : Fact p.Prime] {s z h j : ℚ}
    (a : AdmissiblePair b θ) (pb : p∣b) (p3 : (3:ZMod p)≠0)
    (F : ConicFibre b θ s z h j) : RamifiedRay p θ s := by
  have tn : (θ:ℚ)≠0:=by exact_mod_cast a.2.1.ne'
  have inv : (θ:ℚ)*((s^2/θ*z)/z)=s^2:=by field_simp [F.z_ne]
  have first:=conic_ramified_ray a.1 a.2.2.1 pb F.first
  have second:=conic_ramified_ray a.1 a.2.2.1 pb F.second
  have t : Residue p (θ:ℚ) (θ:ZMod p):=by simpa using residue_int (p:=p) (θ:ℤ)
  have combine {r v : ZMod p} (f : Residue p z r) (g : Residue p (s^2/(θ:ℚ)*z) v)
      (n : r≠0) : Residue p (s^2) ((θ:ZMod p)*(v/r)):=by
    simpa only [inv] using residue_mul t (residue_div g f n)
  rcases first with f|f <;> rcases second with g|g
  · exact Or.inl (by simpa using combine f g one_ne_zero)
  · exact Or.inr (Or.inl (by simpa [mul_comm] using combine f g one_ne_zero))
  · exact Or.inr (Or.inr (by simpa [div_eq_mul_inv] using combine f g (neg_ne_zero.mpr p3)))
  · exact Or.inl (by simpa [p3] using combine f g (neg_ne_zero.mpr p3))

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.conic_anisotropic_unit
#print axioms Sun28.PointLifts.ratio_order
#print axioms Sun28.PointLifts.admissible_ratio_unit
#print axioms Sun28.PointLifts.conic_ramified_ray
#print axioms Sun28.PointLifts.ratio_ramified_ray
