import ScalarPiece07
import SquareProjection
namespace SquareProgram
open CircuitTransport Data

def oldB (d : Rat) := 2401+67830*d
def oldR (d : Rat) := oldB d*(oldB d-1)*(32*oldB d+343)

/-- The actual old 134-coordinate signed instruction, as a polynomial in z²=d. -/
theorem old_492 (d : Rat) (x : Assignment) :
    valueQ source d x 21567=
      ⟨-(x 132)^2+(κ:Rat)*x 133*(oldR d)^3*(oldR d+12701009563200000),0⟩ := by
  rw [OldScalar.v21567]
  dsimp [OldScalar.p21567,oldR,oldB,κ]
  congr 1 <;> grobner

theorem old_label (x : Assignment) : oldB (parameter x)=B (x 1) := by
  have z:=Rat.div_mul_cancel (a:=(Y (x 1))^2) (by decide : (67830:Rat)≠0)
  unfold parameter oldB B;grobner

theorem old_contact (x : Assignment) : oldR (parameter x)=contact (x 1) := by
  unfold oldR contact;rw [old_label]

/-- Before and after changing the positive correction factor r+K to one. -/
theorem exact_change (x : Assignment) :
    valueQ source (parameter x) x 21567=
      ⟨-(x 132)^2+(κ:Rat)*x 133*(contact (x 1))^3*(contact (x 1)+12701009563200000),0⟩ ∧
    let b:=Book.make targetSeed
    let c:=result b source.length (bank source) (table b source) .replace492
    (c.num b).value b x = -(x 132)^2+(κ:Rat)*x 133*(contact (x 1))^3 := by
  constructor
  · rw [old_492,old_contact]
  · exact replaced_signed x
end SquareProgram
