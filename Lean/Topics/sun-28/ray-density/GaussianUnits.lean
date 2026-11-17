import RayFibres
import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace Sun28.RayDensity
open Sun28.MixedSieve QuadraticAlgebra
noncomputable section

abbrev GR (p : ℕ) := QuadraticAlgebra (ZMod p) (-1) 0
abbrev GU (p : ℕ) := (GR p)ˣ
def unitNorm (p : ℕ) : GU p →* (ZMod p)ˣ := Units.map QuadraticAlgebra.norm

def conjugate (p : ℕ) : GU p →* GU p := Units.map
  (show GR p →* GR p from { toFun := star, map_one' := star_one _, map_mul' := fun x y => by simp })

theorem norm_coordinates {p : ℕ} (z : GR p) : z.norm=z.re^2+z.im^2 := by
  simp [norm_def, sq]

def coords {p : ℕ} (z : GU p) : ZMod p × ZMod p := ((z:GR p).re,(z:GR p).im)

def unitOf {p : ℕ} [Fact p.Prime] (x y : ZMod p) (nz : x^2+y^2≠0) : GU p :=
  (QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (isUnit_iff_ne_zero.mpr
    (show (⟨x,y⟩ : GR p).norm≠0 by simpa [norm_coordinates] using nz))).unit

@[simp] theorem val_unitOf {p : ℕ} [Fact p.Prime] (x y : ZMod p) (nz : x^2+y^2≠0) :
    (unitOf x y nz : GR p)=⟨x,y⟩ := IsUnit.unit_spec _

def normFibre (p : ℕ) (t : (ZMod p)ˣ) := {z : GU p // unitNorm p z = t}

def fibreCoords {p : ℕ} [Fact p.Prime] (t : (ZMod p)ˣ) : normFibre p t ≃ Circle p (t:ZMod p) where
  toFun z := ⟨coords z.1, by
    have h := congrArg Units.val z.2
    change (z.1 : GR p).norm = (t:ZMod p) at h
    exact (norm_coordinates _).symm.trans h⟩
  invFun z := ⟨unitOf z.1.1 z.1.2 (z.2.trans_ne t.ne_zero), by
    apply Units.ext
    change _root_.QuadraticAlgebra.norm (unitOf z.1.1 z.1.2 _ : GR p) = _
    simp only [val_unitOf,norm_coordinates]
    exact z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Units.ext
    simp [coords]
  right_inv z := by
    apply Subtype.ext
    simp [coords]

theorem norm_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (unitNorm p) := by
  intro t
  obtain ⟨a,b,h⟩ := ZMod.sq_add_sq p (t:ZMod p)
  let z : Circle p (t:ZMod p) := ⟨(a,b),h⟩
  exact ⟨((fibreCoords t).symm z).1, ((fibreCoords t).symm z).2⟩

def coboundary (p : ℕ) : GU p →* GU p := (MonoidHom.id _)/(conjugate p)

/-- The local conjugation commutators are exactly the kernel of the norm on residue-ring units. -/
theorem range_coboundary {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    (coboundary p).range=(unitNorm p).ker := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    change unitNorm p (x/conjugate p x)=1
    rw [map_div,div_eq_one]
    apply Units.ext
    change (x:GR p).norm=(star (x:GR p)).norm
    simp
  · intro h
    have hz : unitNorm p z=1 := h
    let s := fibreCoords (1:(ZMod p)ˣ) ⟨z,hz⟩
    obtain ⟨a,b,nz,hx,hy⟩ := Sun28.PrimeLower.norm_one_commutator odd s
    refine ⟨unitOf a b nz, ?_⟩
    change unitOf a b nz/conjugate p (unitOf a b nz)=z
    apply (div_eq_iff_eq_mul).mpr
    apply Units.ext
    change (unitOf a b nz:GR p) = (z:GR p)*star (unitOf a b nz:GR p)
    simp only [val_unitOf]
    apply QuadraticAlgebra.ext
    · change a=(z:GR p).re*a+(z:GR p).im*b at hx
      simpa [QuadraticAlgebra.re_mul, mul_assoc] using hx
    · change b=(z:GR p).im*a-(z:GR p).re*b at hy
      simpa [QuadraticAlgebra.im_mul, sub_eq_add_neg, mul_comm, add_comm] using hy

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.fibreCoords
#print axioms Sun28.RayDensity.norm_surjective
#print axioms Sun28.RayDensity.range_coboundary
