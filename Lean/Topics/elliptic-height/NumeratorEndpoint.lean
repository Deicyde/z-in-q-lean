import PhysicalNumerator

namespace EllipticHeight
open StructuralReduction StructuralReduction.Transfer84 PhysicalProjection.Comparison
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.Comparison ProjectionFibres.HeightSupport
open IndependentIndices IndependentIndices.Assembly HeightSpecialization
open QuadraticInt

theorem rational_mul (a b : R) : rational (mul a b)=times (rational a) (rational b) := by
  apply Prod.ext <;> simp [rational,mul,times,Rat.intCast_add,Rat.intCast_mul]

theorem rational_injective {a b : R} (h : rational a=rational b) : a=b :=
  Prod.ext (Rat.intCast_inj.mp (congrArg Prod.fst h)) (Rat.intCast_inj.mp (congrArg Prod.snd h))

def represents (z : Q2) (a b : R) := b≠(0,0) ∧ times z (rational b)=rational a

private theorem regroup (h w v b f : Q2) :
    times (times h (times w v)) (times b f)=times (times w b) (times h (times v f)) := by
  apply Prod.ext <;> dsimp [times] <;> grobner

/-- An integral numerator for one physical abscissa divides the cleared
product whenever its prime divisors are absent from the two denominators. -/
theorem physical_divisibility {x : Fin 84 → Rat} {i : Fin 4} {a b e f : R}
    (hp : represents (roots x i) a b) (hc : represents (rest x i) e f)
    (pr : coprime a (mul b f)) : divides a (numerator x) := by
  apply cancel_denominator pr (c:=mul ((den x:Int),0) e)
  apply rational_injective
  rw [rational_mul,rational_mul,rational_mul,rational_mul,scaled_coeff,split_product x i,regroup,hp.2,hc.2]
  rfl

def label (s : Labels) (i : Fin 4) : Int :=
  match i with
  | 0 => s.n₁
  | 1 => s.n₂
  | 2 => s.n₃
  | _ => s.n₄

theorem largest_label (s : Labels) : ∃ i, (label s i).natAbs=labelSize s := by
  have h (a b : Nat) : max a b=a ∨ max a b=b := by omega
  rcases h s.n₁.natAbs (max s.n₂.natAbs (max s.n₃.natAbs s.n₄.natAbs)) with e|e
  · exact ⟨0,e.symm⟩
  rcases h s.n₂.natAbs (max s.n₃.natAbs s.n₄.natAbs) with f|f
  · exact ⟨1,(e.trans f).symm⟩
  rcases h s.n₃.natAbs s.n₄.natAbs with j|j
  · exact ⟨2,(e.trans (f.trans j)).symm⟩
  · exact ⟨3,(e.trans (f.trans j)).symm⟩

/-- Only the abscissa of a greatest-index point needs a height lower bound. -/
structure PrimitiveFactor (x : Fin 84 → Rat) (s : Labels) where
  row : Fin 4
  largest : (label s row).natAbs=labelSize s
  a : R
  b : R
  e : R
  f : R
  point : represents (roots x row) a b
  others : represents (rest x row) e f
  primeToDenominator : coprime a (mul b f)

theorem greatest_index_bound {x : Fin 84 → Rat} {s : Labels} (dom : domain x)
    (g : PrimitiveFactor x s) (q : Nat)
    (ht : (q^((label s g.row).natAbs^2))^2≤(QuadraticInt.norm g.a).natAbs) : q^((labelSize s)^2)≤J x := by
  rw [g.largest] at ht
  obtain ⟨pos,cap⟩:=numerator_norm_bound dom
  have div:=norm_dvd (physical_divisibility g.point g.others g.primeToDenominator)
  have hi:=Nat.le_of_dvd (Int.natAbs_pos.mpr (Int.ne_of_gt pos)) div
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (Nat.le_trans ht (Nat.le_trans hi cap))

structure NumeratorData (x : Fin 84 → Rat) where
  labels : Labels
  places : ∀ p∈fullPrimes (slope x (tallest x)), Nonempty (SourcePlace x (tallest x) p labels)
  factor : PrimitiveFactor x labels
  height : SlopeHeight x (tallest x)
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  offsetNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int)∣labels.n₂-1

def NumeratorData.integer {x : Fin 84 → Rat} (g : NumeratorData x) (dom : domain x)
    {q : Nat} (two : 2≤q) (growth : (q^((label g.labels g.factor.row).natAbs^2))^2≤(QuadraticInt.norm g.factor.a).natAbs) :
    IntegerData x := by
  refine ⟨g.labels,g.places,?_,g.height,g.oddFirst,g.lastNonzero,g.offsetNonzero,g.anchor⟩
  have h:=greatest_index_bound dom g.factor q growth
  have b:=Nat.pow_le_pow_left two ((labelSize g.labels)^2)
  change 2^((labelSize g.labels)^2)≤64*J x
  omega

theorem circuit_defines_of_one_numerator (marked : Bool) (q : Nat) (two : 2≤q)
    (integerFibres : ∀ n : Nat, circuitImage false (n:Rat))
    (selection : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ Binding.V y 9813=0 ∧
        ∃ g : NumeratorData (decoded y),
          (q^((label g.labels g.factor.row).natAbs^2))^2≤(QuadraticInt.norm g.factor.a).natAbs ∧
          ScalarCondition (decoded y) g.labels.n₂) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply circuit_defines_of_index_height marked integerFibres
  intro T side nz represented
  obtain ⟨y,hy,hz,g,growth,scalar⟩:=selection T side nz represented
  have z:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans hz)
  exact ⟨y,hy,hz,g.integer (fromZero_domain _ false (by simp) z) two growth,scalar⟩

end EllipticHeight

#print axioms EllipticHeight.physical_divisibility
#print axioms EllipticHeight.largest_label
#print axioms EllipticHeight.greatest_index_bound
#print axioms EllipticHeight.NumeratorData.integer
#print axioms EllipticHeight.circuit_defines_of_one_numerator
