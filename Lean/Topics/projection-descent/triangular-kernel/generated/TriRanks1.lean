import TriRanks0
open ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1300000
theorem range80 : ∀ j : Fin 8, boundAt (j.val+80) := by unfold boundAt; decide
theorem range88 : ∀ j : Fin 8, boundAt (j.val+88) := by unfold boundAt; decide
theorem range96 : ∀ j : Fin 8, boundAt (j.val+96) := by unfold boundAt; decide
theorem range104 : ∀ j : Fin 8, boundAt (j.val+104) := by unfold boundAt; decide
theorem range112 : ∀ j : Fin 8, boundAt (j.val+112) := by unfold boundAt; decide
theorem range120 : ∀ j : Fin 8, boundAt (j.val+120) := by unfold boundAt; decide
theorem range128 : ∀ j : Fin 8, boundAt (j.val+128) := by unfold boundAt; decide
theorem range136 : ∀ j : Fin 8, boundAt (j.val+136) := by unfold boundAt; decide
theorem range144 : ∀ j : Fin 8, boundAt (j.val+144) := by unfold boundAt; decide
theorem range152 : ∀ j : Fin 8, boundAt (j.val+152) := by unfold boundAt; decide
end Triangular.Data
