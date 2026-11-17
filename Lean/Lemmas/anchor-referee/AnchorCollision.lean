import CollisionRows

namespace AnchorCollision
open StructuralReduction StructuralReduction.Transfer84
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.Comparison EllipticHeight.Labels
open PhysicalProjection.Comparison PhysicalProjection.RootOrdinate AnchorCircuit

private theorem nonzeroNorm {a : Q2} (nz : a≠(0,0)) : norm a≠0 := by
  intro h
  obtain ⟨h₀,h₁⟩:=(CircuitTransport.Quadratic.norm_zero_iff a.1 a.2).mp h
  exact nz (Prod.ext h₀ h₁)

private theorem mul_nonzero {a b : Q2} (az : a≠(0,0)) (bz : b≠(0,0)) :
    times a b≠(0,0) := by
  have n : norm a*norm b≠0 :=
    fun h => (Rat.mul_eq_zero.mp h).elim (nonzeroNorm az) (nonzeroNorm bz)
  intro zero
  rw [←norm_product,zero] at n
  exact n (by dsimp [norm];grobner)

private theorem scalar_nonzero_pair {x : Fin 84→Rat} (zero : output false x=0) :
    (cell x 25,cell x 26)≠(0,0) := by
  intro eq
  have u:=congrArg Prod.fst eq
  have v:=congrArg Prod.snd eq
  change cell x 25=0 at u
  change cell x 26=0 at v
  have az : A x=0 := by dsimp only [A];rw [u,v];grobner
  have rows:=signed_zero x false (by simp) zero
  have h:=(equation_num x).mp (rows 1072 (by decide))
  rw [az] at h
  have rn : r x≠0 := by have :=r_positive x;grind
  have powNz {t : Rat} (ht : t≠0) (n : Nat) : t^n≠0 := by
    induction n with
    | zero => rw [Rat.pow_zero];decide
    | succ k ih => rw [Rat.pow_succ];exact fun t=> (Rat.mul_eq_zero.mp t).elim ih ht
  have L : (r x)^16≠0 := powNz rn 16
  have dz:=(Rat.mul_eq_zero.mp h).resolve_right L
  have rep:=(equation_rec x).mp (rows 1038 (by decide))
  rw [dz] at rep
  have mul : (r x)^3*(q x)^2=0 := by grobner
  have qq:=(Rat.mul_eq_zero.mp mul).resolve_left (powNz rn 3)
  exact (powNz (physical_norm x (rows 513 (by decide))) 2) qq

private theorem rawRoot_nonzero {x : Fin 84→Rat} (zero : output false x=0) :
    (cell x 5,cell x 6)≠(0,0) := by
  have live:=delta_scalar_nonzero (chart_equations zero (1:Fin 4))
  intro eq;apply live
  have h₀:=congrArg Prod.fst eq
  have h₁:=congrArg Prod.snd eq
  change cell x 5=0 at h₀
  change cell x 6=0 at h₁
  change (atWire x 182*cell x 5,atWire x 182*cell x 6)=(0,0)
  rw [h₀,h₁,Rat.mul_zero]

/-- The subtraction numerator is nonzero on the complete 84-coordinate ordinary locus. -/
theorem numerator_ne84 {x : Fin 84→Rat} (zero : output false x=0) :
    numerator (rootH x 1) (rootJ x 1)≠(0,0) := by
  intro bad
  obtain ⟨g₀,g₁⟩:=zeroReciprocals x bad
  have rows:=signed_zero x false (by simp) zero
  have left:=rows 677 (by decide)
  have right:=rows 782 (by decide)
  rw [ratio677 x g₀ g₁] at left
  rw [ratio782 x g₀ g₁] at right
  have pz : product x=(0,0) := Prod.ext
    ((Rat.mul_eq_zero.mp left).resolve_left (factor_nonzero x))
    ((Rat.mul_eq_zero.mp right).resolve_left (factor_nonzero x))
  exact (mul_nonzero (mul_nonzero (a:=(5521,-3576)) (by decide) (rawRoot_nonzero zero))
    (scalar_nonzero_pair zero)) pz

/-- The two affine coordinates of Q₂ cannot agree simultaneously with the coordinates of P. -/
theorem excludes_P84 {x : Fin 84→Rat} (zero : output false x=0) :
    ¬ (sq (rootH x 1)=sq ((-1,7/4):Q2) ∧
      times (rootH x 1) (rootJ x 1)=times ((-1,7/4):Q2) (39/8,-9/2)) := by
  rintro ⟨xe,ye⟩
  have h0:=delta_scalar_nonzero (chart_equations zero (1:Fin 4))
  have nz:=mul_nonzero h0 (numerator_ne84 zero)
  apply nz
  have ab (h j a b : Q2) (xx:sq h=sq a) (yy:times h j=times a b) :
      times h (sub (times a j) (times b h))=(0,0) := by
    have t:times h (sub (times a j) (times b h))=
        sub (times a (times h j)) (times b (sq h)) := by
      apply Prod.ext <;> dsimp [sq,times,sub] <;> grobner
    rw [t,xx,yy]
    apply Prod.ext <;> dsimp [sq,times,sub] <;> grobner
  exact ab _ _ _ _ xe ye

theorem excludes_marked_P84 {x : Fin 84→Rat} (active : cell x 1≠0) (zero : output true x=0) :
    ¬ (sq (rootH x 1)=sq ((-1,7/4):Q2) ∧
      times (rootH x 1) (rootJ x 1)=times ((-1,7/4):Q2) (39/8,-9/2)) := by
  apply excludes_P84
  apply (signed84 archiveAt x).1.mpr
  exact ((signed84 archiveAt x).2.mp zero).resolve_left active

theorem excludes_P80 (y : Fin 80→Rat) (zero : Binding.V y 9813=0) :
    ¬ (sq (rootH (decoded y) 1)=sq ((-1,7/4):Q2) ∧
      times (rootH (decoded y) 1) (rootJ (decoded y) 1)=times ((-1,7/4):Q2) (39/8,-9/2)) :=
  excludes_P84 (ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans zero))

theorem excludes_marked_P80 (y : Fin 80→Rat) (active : y 0≠0) (zero : Binding.V y 9814=0) :
    ¬ (sq (rootH (decoded y) 1)=sq ((-1,7/4):Q2) ∧
      times (rootH (decoded y) 1) (rootJ (decoded y) 1)=times ((-1,7/4):Q2) (39/8,-9/2)) := by
  have p := (Binding.physical_pointwise true y).symm.trans zero
  change y 0 * output80 false y=0 at p
  exact excludes_P84 (ordinary_decoded y ((Rat.mul_eq_zero.mp p).resolve_left active))

#print axioms numerator_ne84
#print axioms excludes_P84
#print axioms excludes_marked_P84
#print axioms excludes_P80
#print axioms excludes_marked_P80
end AnchorCollision
