import IdealRepresentative
import RayInterpretation

namespace Sun28.Reciprocity
open Sun28.RayDensity Sun28.RayDensity.Artin
noncomputable section
variable {I:Type*} [Fintype I] (q:I→ℕ) [∀i,Fact (q i).Prime]
variable (cop:Pairwise (Function.onFun Nat.Coprime (levels q)))

/-- Coefficientwise Gaussian conjugation, on actual ideals. -/
def conjugateRing : GaussianInt →+* GaussianInt where
  toFun:=star
  map_one':=star_one _
  map_zero':=star_zero _
  map_add':=star_add
  map_mul' x y:=by simp

omit [Fintype I] in
theorem tuple_conjugate (a b:ℤ) (dy:((a:ZMod 16),(b:ZMod 16))∈primarySet)
    (odd:∀i,(a:ZMod (q i))^2+(b:ZMod (q i))^2≠0) :
    ∃ (dy':((a:ZMod 16),((-b:ℤ):ZMod 16))∈primarySet)
      (odd':∀i,(a:ZMod (q i))^2+((-b:ℤ):ZMod (q i))^2≠0),
      primeTuple q a (-b) dy' odd' = joinedAut q dyadicConj (primeTuple q a b dy odd) := by
  have dy' : ((a:ZMod 16),((-b:ℤ):ZMod 16))∈primarySet := by
    simpa [conjPair] using primary_operations.2.1 _ dy
  have odd' (i:I) : (a:ZMod (q i))^2+((-b:ℤ):ZMod (q i))^2≠0 := by simpa using odd i
  refine ⟨dy',odd',Prod.ext ?_ (funext (fun i=>?_))⟩
  · apply Subtype.ext;apply Prod.ext;rfl;exact Int.cast_neg _
  · apply Units.ext
    change (unitOf (p:=q i) a ((-b:ℤ):ZMod (q i)) (odd' i):GR (q i))=star (unitOf (p:=q i) a b (odd i):GR (q i))
    rw [val_unitOf,val_unitOf]
    apply QuadraticAlgebra.ext <;> simp

theorem conjugate_ideal (J:coprimeIdeals (M q)) :
    ∃ K:coprimeIdeals (M q), K.val = J.val.map conjugateRing ∧
      idealCoordinates q cop (K:idealRay q) =
        joinedAut q dyadicConj (idealCoordinates q cop (J:idealRay q)) := by
  obtain ⟨z,dy,odd,hJ,_,hJc⟩:=prime_ideal_data q cop J
  obtain ⟨dy',odd',eq⟩:=tuple_conjugate q z.re z.im dy odd
  let w:GaussianInt:=star z
  have hd : ((w.re:ZMod 16),(w.im:ZMod 16))∈primarySet := dy'
  let K:=principalIdeal q w (generator_unit q cop w hd odd')
  refine ⟨K,?_,?_⟩
  · rw [←hJ,Ideal.map_span,Set.image_singleton]
    rfl
  · rw [hJc]
    exact (idealCoordinates_generator q cop w hd odd').trans eq

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.tuple_conjugate
#print axioms Sun28.Reciprocity.conjugate_ideal
