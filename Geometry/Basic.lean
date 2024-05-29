
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Angle.Sphere

open EuclideanGeometry Real FiniteDimensional AffineSubspace Affine.Simplex

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

[Fact (finrank ℝ V = 2)] (A B C : P)

#check ∠ A B C

/-- easy to prove from Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius; is switching from oriented to unoriented angle-/
theorem Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius
    (t : Affine.Triangle ℝ P) {i₁ : Fin 3} {i₂ : Fin 3} {i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.points i₃) / (angle (t.points i₁) (t.points i₂) (t.points i₃)).sin
    = 2 * Affine.Simplex.circumradius t :=
  sorry

theorem affineIndependent_of_not_collinear_vector (hCol : ¬ Collinear ℝ ({A, B, C}: Set P)) :
    AffineIndependent ℝ ![A, B, C] := by
  rw [affineIndependent_iff_not_collinear_of_ne]
  have : ({A, B, C}: Set P) = {![A, B, C] 0, ![A, B, C] 1, ![A, B, C] 2} := by aesop
  rw [this] at hCol
  convert hCol
  simp
  simp
  simp

/-- Circumcenter as a point of intersection of perpendicular bisectors of triangle-/
theorem circumcenter_perpendicular_bisector (hCol : ¬ Collinear ℝ ({A, B, C}: Set P)) :
    circumcenter ⟨![A, B, C], affineIndependent_of_not_collinear_vector A B C hCol⟩
      ∈ perpBisector A B:= by
  have distA:= dist_circumcenter_eq_circumradius ⟨![A, B, C], affineIndependent_of_not_collinear_vector A B C hCol⟩ 0
  simp at distA
  have distB:= dist_circumcenter_eq_circumradius ⟨![A, B, C], affineIndependent_of_not_collinear_vector A B C hCol⟩ 1
  simp at distB
  set O := circumcenter ⟨![A, B, C], affineIndependent_of_not_collinear_vector A B C hCol⟩
  have distAB : dist A O = dist B O := by
    rw[distA]
    rw[distB]
  exact mem_perpBisector_iff_dist_eq'.mpr distAB


/-- Rule of sines at A and B.-/
theorem rule_of_sines (hAC : A ≠ C) (hBC : B ≠ C) :
    dist B C / sin (∠ B A C) = dist A C / sin (∠ A B C) := by
  by_cases hCol : Collinear ℝ ({A, B, C}: Set P)
  · sorry
  let s := circumsphere ⟨![A, B, C], affineIndependent_of_not_collinear_vector A B C hCol⟩
  have h2r := Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius
    ⟨![A, B, C], affineIndependent_of_not_collinear_vector A B C hCol⟩ (i₁ := 0) (i₂ := 1) (i₃ := 2)
    (by simp) (by simp) (by simp)
  simp at h2r
  have h2r' := Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius
    ⟨![A, B, C], affineIndependent_of_not_collinear_vector A B C hCol⟩ (i₁ := 1) (i₂ := 0) (i₃ := 2)
    (by simp) (by simp) (by simp)
  simp at h2r'
  set T : Affine.Triangle ℝ P := ⟨![A, B, C], affineIndependent_of_not_collinear_vector A B C hCol⟩
  rw[h2r]
  rw[h2r']

theorem rule_of_sines' (hBA: B ≠ A) (hCA : C ≠ A): dist A C / sin (∠ A B C) = dist A B / sin (∠ A C B) := by
  have := rule_of_sines B C A hBA hCA
  rw [dist_comm, dist_comm A, angle_comm, angle_comm A]
  exact this


theorem angle_bisector (X : P) (hCol : ¬ Collinear ℝ ({A, B, C}: Set P))(h1 : ∠ B A X = ∠ X A C) (h2 : Collinear ℝ ({B, X, C} : Set P)) : dist A B / dist B X = dist A C / dist C X := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear hCol
  have hBC : B ≠ C := ne₂₃_of_not_collinear hCol
  have hAC : A ≠ C := ne₁₃_of_not_collinear hCol
  have hCA : C ≠ A := hAC.symm
  have hXB : X ≠ B := by sorry
  have hXC : X ≠ C := by sorry
  have hXA : X ≠ A := by sorry
  have hAXB : ∠ A X B ≠ 0 := by sorry
  have hBXC : ∠ B X C ≠ 0 := by sorry
  have hXAC : ∠ X A C ≠ 0 := by sorry
  have hAXC : ∠ A X C ≠ 0 := by sorry
  have hXAB : ∠ X A B ≠ 0 := by
    rw[angle_comm]
    rw[h1]
    exact hXAC
  have h3 : (∠ X A B).sin ≠ 0 := by
    intro sineq
    rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi] at sineq
    rcases sineq with sineqa |sineqb
    · contradiction
    · have picoll := collinear_of_angle_eq_pi sineqb
      sorry
  have h4 : (∠ A X B).sin ≠ 0 := by sorry
  have h5 : (∠ X A C).sin ≠ 0 := by sorry
  have h6 : (∠ A X C).sin ≠ 0 := by sorry
  have h7 : dist X B ≠ 0 := by
    rw [dist_ne_zero]
    exact hXB
  have h8 : dist X C ≠ 0 := by
    rw [dist_ne_zero]
    exact hXC
  calc
    dist A B / dist B X
      = sin (∠ A X B) / sin (∠ X A B) := by
        have := rule_of_sines A X B hAB hXB
        rw [dist_comm B]
        field_simp at this ⊢
        rw [mul_comm (∠ A X B).sin]
        exact this.symm
    _ = sin (∠ A X C) / sin (∠ X A C) := by
      congrm ?_/?_
      · rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi] at h2
        simp only [hXB.symm, hXC.symm, false_or] at h2
        rcases h2 with h2a | h2b
        · contradiction
        rw [← sin_pi_sub]
        congrm sin ?_
        have := angle_add_angle_eq_pi_of_angle_eq_pi A h2b
        linarith
      · rw [angle_comm, h1]
    _ = dist A C / dist C X := by
      have := rule_of_sines A X C hCA.symm hXC
      rw [dist_comm C]
      field_simp at this ⊢
      rw [mul_comm (∠ A X C).sin]
      exact this

theorem exists_incentre : ∃ (X : P), (∠ B A X = ∠ X A C) ∧ (∠ A C X = ∠ X C B) ∧ (∠ C B X = ∠ X B A) := by sorry
-- theorem exists_incentre' :

theorem morley (X Y Z : P) (hA1 : ∠ B A X = ∠ X A Z) (hA2 : ∠ X A Z = ∠ Z A C) (hB1 : ∠ A B X = ∠ X B Y) (hB2 : ∠ X B Y = ∠ Y B C) (hC1 : ∠ B C Y = ∠ Y C Z) (hC2 : ∠ Y C Z = ∠ Z C A) : dist X Y = dist Y Z ∧ dist Y Z = dist Z X := by sorry
