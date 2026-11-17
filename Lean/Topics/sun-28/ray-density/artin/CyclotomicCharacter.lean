import PrimaryGroup

namespace Sun28.RayDensity.Artin
open SemidirectProduct
noncomputable section
variable {I:Type*} (q:I→ℕ) [∀i,Fact (q i).Prime]
abbrev Residues := (ZMod 32)ˣ × ((i:I)→(ZMod (q i))ˣ)
abbrev RayUnits := Primary × ((i:I)→GU (q i))
abbrev rayAction := act (joinedAut q dyadicConj) (joined_involution q dyadicConj dyadic_involution)
abbrev RayGroup := SemidirectProduct (RayUnits q) C₂ (rayAction q)

def residueNorm : RayUnits q →* Residues q where
  toFun a := (dyadicNorm a.1,fun i=>unitNorm (q i) (a.2 i))
  map_one' := by ext <;> simp
  map_mul' x y := by apply Prod.ext; exact map_mul _ _ _; exact funext (fun _=>map_mul _ _ _)

theorem residueNorm_fixed (c : C₂) (a:RayUnits q) :
    residueNorm q (rayAction q c a)=residueNorm q a := by
  rcases two_cases c with rfl|rfl
  · simp
  · have hw : (rayAction q flip) a=joinedAut q dyadicConj a := by
      change (if flip=1 then (1:MulAut (RayUnits q)) else joinedAut q dyadicConj) a=joinedAut q dyadicConj a
      rw [ite_eq_right (by decide : flip≠1)]
    rw [hw]
    apply Prod.ext
    · apply Units.ext
      exact (dyadic_tables.2.2.1 _ a.1.2).1
    · apply funext
      intro i
      apply Units.ext
      change (star (a.2 i:GR (q i))).norm=(a.2 i:GR (q i)).norm
      simp

def signUnit (m:ℕ) : C₂→* (ZMod m)ˣ where
  toFun c := if c=1 then 1 else -1
  map_one' := by simp
  map_mul' a b := by
    have n : flip≠1 := by decide
    have e : flip*flip=1 := by decide
    rcases two_cases a with rfl|rfl <;> rcases two_cases b with rfl|rfl <;> simp [n,e]

def signTuple : C₂→* Residues q where
  toFun c := (signUnit 32 c, fun i=>signUnit (q i) c)
  map_one' := by apply Prod.ext; exact map_one _; exact funext (fun _=>map_one _)
  map_mul' a b := by apply Prod.ext; exact map_mul _ _ _; exact funext (fun _=>map_mul _ _ _)

/-- The extension of the Gaussian norm sends complex conjugation to inversion
on roots of unity, that is, exponent −1 at every rational factor. -/
def rationalCharacter : RayGroup q →* Residues q where
  toFun g := residueNorm q g.left * signTuple q g.right
  map_one' := by simp
  map_mul' a b := by
    change residueNorm q (a.left*(rayAction q a.right) b.left) *
       signTuple q (a.right*b.right) = _ * _
    rw [map_mul,map_mul,residueNorm_fixed]
    ac_rfl

theorem character_on_even (a:RayUnits q) : rationalCharacter q (inl a)=residueNorm q a := by
  change _ * signTuple q 1=_
  simp

theorem character_on_conjugation : rationalCharacter q (inr flip)=
    ((-1:(ZMod 32)ˣ),fun i=>(-1:(ZMod (q i))ˣ)) := by
  change residueNorm q 1 * signTuple q flip = _
  rw [map_one,one_mul]
  change (signUnit 32 flip,fun i=>signUnit (q i) flip)=_
  simp [signUnit, (by decide : flip≠1)]

theorem orientation (u:(ZMod 32)ˣ) : (u:ZMod 32).val%4=1 ∨ (-(u:ZMod 32)).val%4=1 := by
  revert u
  decide


theorem rational_surjective : Function.Surjective (rationalCharacter q) := by
  rintro ⟨u,v⟩
  rcases orientation u with h|h
  · obtain ⟨a,ea⟩:=(dyadic_range u).2 h
    choose b eb using fun i=>norm_surjective (q i) (v i)
    refine ⟨inl (a,b),?_⟩
    rw [character_on_even]
    exact Prod.ext ea (funext eb)
  · obtain ⟨a,ea⟩:=(dyadic_range (-u)).2 h
    choose b eb using fun i=>norm_surjective (q i) (-v i)
    refine ⟨inl (a,b)*inr flip,?_⟩
    rw [map_mul,character_on_even,character_on_conjugation]
    apply Prod.ext
    · change dyadicNorm a * (-1)=u
      rw [ea];simp
    · apply funext
      intro i
      change unitNorm (q i) (b i)*(-1)=_
      rw [eb];simp

/-- The entire derived subgroup is the kernel of the rational character for
any collection of odd residue primes. No finite class-field hypothesis enters. -/
theorem rational_kernel (odd:∀i,q i≠2) :
    (rationalCharacter q).ker=commutator (RayGroup q) := by
  rw [full_ray_derived q dyadicConj dyadic_involution odd,dyadic_kernel]
  ext g
  constructor
  · intro good
    have key : rationalCharacter q g=1 := good
    have right : g.right=1 := by
      rcases two_cases g.right with e|e
      · exact e
      · exfalso
        have term := congrArg Prod.fst key
        change dyadicNorm g.left.1 * signUnit 32 g.right=1 at term
        rw [e] at term
        have sg : signUnit 32 flip=-1 := by decide
        rw [sg,mul_neg_one] at term
        have minus : (dyadicNorm g.left.1 :ZMod 32) = -1 := by
          have hh:=congrArg Units.val term
          change -(dyadicNorm g.left.1 :ZMod 32)=1 at hh
          exact neg_eq_iff_eq_neg.mp hh
        have r := (dyadic_range _).1 ⟨g.left.1,rfl⟩
        rw [minus] at r
        exact (by decide : ¬ ((-1:ZMod 32).val%4=1)) r
    change residueNorm q g.left * signTuple q g.right=1 at key
    rw [right,map_one,mul_one] at key
    refine ⟨g.left,⟨congrArg Prod.fst key,?_⟩,?_⟩
    · exact fun i _=>congrFun (congrArg Prod.snd key) i
    · apply SemidirectProduct.ext <;> simp [right]
  · rintro ⟨a,⟨d,other⟩,rfl⟩
    change rationalCharacter q (inl a)=1
    rw [character_on_even]
    exact Prod.ext d (funext (fun i=>other i (Set.mem_univ i)))

/-- The finite abelianization in explicit CRT coordinates. -/
def rationalAbelianization (odd:∀i,q i≠2) : (RayGroup q ⧸ commutator (RayGroup q)) ≃* Residues q :=
  (QuotientGroup.quotientMulEquivOfEq (rational_kernel q odd).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (rationalCharacter q) (rational_surjective q))

end
end Sun28.RayDensity.Artin
#print axioms Sun28.RayDensity.Artin.residueNorm_fixed
#print axioms Sun28.RayDensity.Artin.character_on_even
#print axioms Sun28.RayDensity.Artin.character_on_conjugation
#print axioms Sun28.RayDensity.Artin.orientation
#print axioms Sun28.RayDensity.Artin.rational_surjective
#print axioms Sun28.RayDensity.Artin.rational_kernel
#print axioms Sun28.RayDensity.Artin.rationalAbelianization
