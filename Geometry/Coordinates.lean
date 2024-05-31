import Mathlib

noncomputable section

open InnerProductGeometry
open RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V}

/-- Angles are equal if the underlying algebraic expressions are. -/
theorem angle_eq_angle_of_squares (x y z w : V)
    (h : ⟪x, y⟫^2 / (⟪x, x⟫ * ⟪y, y⟫) = ⟪z, w⟫^2 / (⟪z, z⟫ * ⟪w, w⟫)) :
    angle x y = angle z w :=
  sorry

variable (x y z : EuclideanSpace ℝ (Fin 2))

def perimeter : ℝ := dist y z  + dist z x + dist x y

def incentre : EuclideanSpace ℝ (Fin 2) :=
  (dist y z / perimeter x y z) • x + (dist z x / perimeter x y z) • y + (dist x y / perimeter x y z) • z

set_option maxHeartbeats 5000000
example : angle (incentre x y z - x) (y - x) = angle (incentre x y z - x) (z - x) := by
  apply angle_eq_angle_of_squares
  have : (y 0 - x 0) * (y 0 - x 0) + (y 1 - x 1) * (y 1 - x 1) ≠ 0 := sorry
  have : (dist y z * x 0 + dist z x * y 0 + dist x y * z 0 - (dist y z + dist z x + dist x y) * x 0) *
            (dist y z * x 0 + dist z x * y 0 + dist x y * z 0 - (dist y z + dist z x + dist x y) * x 0) +
          (dist y z * x 1 + dist z x * y 1 + dist x y * z 1 - (dist y z + dist z x + dist x y) * x 1) *
            (dist y z * x 1 + dist z x * y 1 + dist x y * z 1 - (dist y z + dist z x + dist x y) * x 1) ≠ 0 := sorry
  have : (z 0 - x 0) * (z 0 - x 0) + (z 1 - x 1) * (z 1 - x 1) ≠ 0 := sorry
  have : (dist y z * x 0 + dist z x * y 0 + dist x y * z 0 - (dist y z + dist z x + dist x y) * x 0) *
            (dist y z * x 0 + dist z x * y 0 + dist x y * z 0 - (dist y z + dist z x + dist x y) * x 0) +
          (dist y z * x 1 + dist z x * y 1 + dist x y * z 1 - (dist y z + dist z x + dist x y) * x 1) *
            (dist y z * x 1 + dist z x * y 1 + dist x y * z 1 - (dist y z + dist z x + dist x y) * x 1) ≠ 0 := sorry
  have : perimeter x y z ≠ 0 := sorry
  have hxy : dist x y ^ 2 = ⟪x - y, x - y⟫ := by rw [dist_eq_norm, real_inner_self_eq_norm_sq]
  have hyz : dist y z ^ 2 = ⟪y - z, y - z⟫ := by rw [dist_eq_norm, real_inner_self_eq_norm_sq]
  have hzx : dist z x ^ 2 = ⟪z - x, z - x⟫ := by rw [dist_eq_norm, real_inner_self_eq_norm_sq]
  dsimp [incentre, perimeter, angle, -ne_eq] at *
  simp only [map_sub, map_add, map_mul, map_div₀, conj_trivial, Fin.sum_univ_two, dist_comm] at *
  field_simp
  -- polyrith
  sorry
