import DyadicCharacter
import OddRayGroup

namespace Sun28.RayDensity.Artin

abbrev Primary := ↥primarySet

private theorem times_one (a:Pair 16) : times a (1,0)=a := by ext <;> simp [times]
private theorem one_times (a:Pair 16) : times (1,0) a=a := by ext <;> simp [times]
private theorem times_assoc (a b c:Pair 16) : times (times a b) c=times a (times b c) := by
  apply Prod.ext <;> dsimp [times] <;> ring
private theorem times_comm (a b:Pair 16) : times a b=times b a := by
  apply Prod.ext <;> dsimp [times] <;> ring
private theorem conj_times (a b:Pair 16) : conjPair (times a b)=times (conjPair a) (conjPair b) := by
  apply Prod.ext <;> dsimp [times,conjPair] <;> ring

instance : CommGroup Primary where
  mul a b := ⟨times a b,primary_operations.2.2.2 _ a.2 _ b.2⟩
  one := ⟨(1,0),primary_operations.1⟩
  inv a := ⟨inverse16 a,(primary_operations.2.2.1 _ a.2).1⟩
  one_mul a := Subtype.ext (one_times _)
  mul_one a := Subtype.ext (times_one _)
  mul_assoc a b c := Subtype.ext (times_assoc _ _ _)
  mul_comm a b := Subtype.ext (times_comm _ _)
  inv_mul_cancel a := Subtype.ext ((primary_operations.2.2.1 _ a.2).2)

def dyadicConj : MulAut Primary where
  toFun a := ⟨conjPair a,primary_operations.2.1 _ a.2⟩
  invFun a := ⟨conjPair a,primary_operations.2.1 _ a.2⟩
  left_inv a := by apply Subtype.ext; apply Prod.ext <;> simp [conjPair]
  right_inv a := by apply Subtype.ext; apply Prod.ext <;> simp [conjPair]
  map_mul' a b := Subtype.ext (conj_times _ _)

theorem dyadic_involution : dyadicConj*dyadicConj=1 := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  apply Prod.ext <;> simp [dyadicConj,conjPair]

def normUnit (a : Primary) : (ZMod 32)ˣ where
  val := norm32 a
  inv := norm32 a ^ 7
  val_inv := by simpa only [pow_succ',pow_zero,mul_one] using (dyadic_tables.2.2.1 _ a.2).2
  inv_val := by simpa only [pow_succ,pow_zero,one_mul] using (dyadic_tables.2.2.1 _ a.2).2

def dyadicNorm : Primary →* (ZMod 32)ˣ where
  toFun := normUnit
  map_one' := by apply Units.ext; decide
  map_mul' a b := Units.ext (norm32_times a b)

/-- Equality with an actual subgroup of the group, rather than a count of coordinate pairs. -/
theorem dyadic_kernel : (delta dyadicConj).range=dyadicNorm.ker := by
  ext z
  have hcoord (a:Primary) : ((delta dyadicConj a:Primary):Pair 16) = ratioPair 3 a := by
    change ((a/dyadicConj a:Primary):Pair 16)=_
    rw [div_eq_mul_inv]
    exact dyadic_tables.2.2.2 _ a.2
  constructor
  · rintro ⟨a,rfl⟩
    apply Units.ext
    change norm32 ((delta dyadicConj a:Primary):Pair 16)=1
    have h : ratioPair 3 a∈primarySet.image (ratioPair 3) := Finset.mem_image_of_mem _ a.2
    rw [dyadic_tables.2.1] at h
    exact (hcoord a ▸ (Finset.mem_filter.mp h).2 : _)
  · intro h
    have v : norm32 z=1 := congrArg Units.val (show dyadicNorm z=1 from h)
    have incl : (z:Pair 16) ∈ primarySet.filter (fun u=>norm32 u=1) :=
      Finset.mem_filter.mpr ⟨z.2,v⟩
    rw [←dyadic_tables.2.1] at incl
    obtain ⟨a,ha,e⟩:=Finset.mem_image.mp incl
    exact ⟨⟨a,ha⟩,Subtype.ext ((hcoord ⟨a,ha⟩).trans e)⟩

/-- All and only the eight unit classes over 1 modulo 4 occur. -/
theorem dyadic_range (u : (ZMod 32)ˣ) :
    u∈dyadicNorm.range ↔ (u:ZMod 32).val % 4=1 := by
  have h:=dyadic_tables.1
  constructor
  · rintro ⟨a,rfl⟩
    have m : norm32 a∈primarySet.image norm32 := Finset.mem_image_of_mem _ a.2
    rw [h] at m
    exact (Finset.mem_filter.mp m).2
  · intro hu
    have m : (u:ZMod 32)∈Finset.univ.filter (fun r:ZMod 32=>r.val %4=1) := by simpa using hu
    rw [←h] at m
    obtain ⟨a,ha,e⟩:=Finset.mem_image.mp m
    exact ⟨⟨a,ha⟩,Units.ext e⟩

end Sun28.RayDensity.Artin
#print axioms Sun28.RayDensity.Artin.dyadic_involution
#print axioms Sun28.RayDensity.Artin.dyadic_kernel
#print axioms Sun28.RayDensity.Artin.dyadic_range
