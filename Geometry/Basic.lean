
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
  · have hCol1 : A = B ∨ C = B ∨ ∠ A B C = 0 ∨ ∠ A B C = π := by
      rw[collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi] at hCol
      exact hCol
    have hColBC : Collinear ℝ {B, A, C} := by
      convert hCol using 1
      aesop
    rw[collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi] at hColBC
    obtain hAB | hCB | hang0orpi := hCol1
    · rw[hAB]
    · rw[hCB] at hBC
      contradiction
    --sorry
    obtain  hBA | hCA| h3 := hColBC
    · rw[hBA]
    · rw[hCA] at hAC
      contradiction
    · have hangBAC0 : (∠ B A C).sin = 0 := by
        exact sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi.mpr h3
      have hangABC0 : (∠ A B C).sin = 0 := by
        exact sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi.mpr hang0orpi
      rw[hangBAC0]
      rw[hangABC0]
      simp
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

theorem injectivity_of_sines_on_interval (x y : ℝ) (h1x: x ≥ 0)
(h1y: y ≥ 0)(h2: x + y < π)(h3: x.sin = y.sin): x=y := by sorry


#check angle_add_angle_add_angle_eq_pi
#check angle_nonneg
#check angle_le_pi

theorem angle_eq_zero_or_pi_of_angle_eq_pi (hAC: A ≠ C) (hzero : ∠ A B C = 0) : ∠ A C B = 0 ∨ ∠ A C B = π := by sorry

theorem angle_bisector (X : P) (hCol : ¬ Collinear ℝ ({A, B, C}: Set P))(hbetween : Wbtw ℝ B X C) : dist A B / dist B X = dist A C / dist C X ↔ ∠ B A X = ∠ X A C := by
  have h2 : Collinear ℝ ({B, X, C} : Set P) := Wbtw.collinear hbetween
  have hAB : A ≠ B := ne₁₂_of_not_collinear hCol
  have hBC : B ≠ C := ne₂₃_of_not_collinear hCol
  have hAC : A ≠ C := ne₁₃_of_not_collinear hCol
  have hCA : C ≠ A := hAC.symm
  have hXB : X ≠ B := by sorry
  have hXC : X ≠ C := by sorry
  have hXA : X ≠ A := by sorry
  have hXABnotcol : ¬ Collinear ℝ ({X, A, B}: Set P) := by
    intro hXABcol
    have i0 : Collinear ℝ {A, B, X, C} := by
      have i1 : B ∈ ({B, X, C} : Set P) := by simp_all only [ne_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, or_false, true_or]
      have i2 : X ∈ ({B, X, C} : Set P) := by simp_all only [ne_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, or_false, true_or, or_true]
      rw [Collinear.collinear_insert_iff_of_ne h2 i1 i2 hXB.symm]
      have i3: ({A, B, X} : Set P) = {X, A, B} := by aesop
      rw [i3]
      exact hXABcol
    have : Collinear ℝ {A, B, C} := by
      have : ({A, B, C} : Set P) ⊆ {A, B, X, C} := by simp_all only [ne_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, or_self, not_false_eq_true, Set.insert_subset_insert_iff,
        Set.subset_insert]
      apply Collinear.subset this i0
    contradiction

  have h3 : (∠ X A B).sin ≠ 0 := sorry
  have h4 : (∠ A X B).sin ≠ 0 := by sorry
  have h5 : (∠ X A C).sin ≠ 0 := by sorry
  have h6 : (∠ A X C).sin ≠ 0 := by sorry
  have hXAB : ∠ X A B ≠ 0 := by apply angle_ne_zero_of_not_collinear hXABnotcol
  have hXABpi : ∠ X A B ≠ π := by apply angle_ne_pi_of_not_collinear hXABnotcol
  have hAXBnotcol : ¬ Collinear ℝ ({A, X, B}: Set P) := by
    have : ({A, X, B} : Set P) = {X, A, B} := by aesop
    rw[this]
    exact hXABnotcol
  have hAXBpi : ∠ A X B ≠ π := by apply angle_ne_pi_of_not_collinear hAXBnotcol
  have hBXC : ∠ B X C ≠ 0 := by sorry
  have hBXCpi : ∠ B X C ≠ π := by sorry
  have hAXCnotcol : ¬ Collinear ℝ ({A, X, C}: Set P) := by
    intro hAXCcol
    have i0 : Collinear ℝ {A, B, X, C} := by
      have i1 : C ∈ ({B, X, C} : Set P) := by simp_all only [ne_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, or_true]
      have i2 : X ∈ ({B, X, C} : Set P) := by simp_all only [ne_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, or_false, true_or, or_true]
      rw [Collinear.collinear_insert_iff_of_ne h2 i1 i2 hXC.symm]
      have i3: ({A, C, X} : Set P) = {A, X, C} := by aesop
      rw [i3]
      exact hAXCcol
    have : Collinear ℝ {A, B, C} := by
      have : ({A, B, C} : Set P) ⊆ {A, B, X, C} := by simp_all only [ne_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, or_self, not_false_eq_true, Set.insert_subset_insert_iff,
        Set.subset_insert]
      apply Collinear.subset this i0
    contradiction
  have hAXC : ∠ A X C ≠ 0 := by apply angle_ne_zero_of_not_collinear hAXCnotcol
  have hAXCpi : ∠ A X C ≠ π := by apply angle_ne_pi_of_not_collinear hAXCnotcol
  constructor
  -- reverse direction starts here
  · intro h
    -- showing equality of sines
    have H :=
    calc
      (∠ B A X).sin = dist B X / dist A B * (∠ A X B).sin := by
        have hrosXAB := rule_of_sines X A B hXB hAB
        have : dist A B ≠ 0 := by exact dist_ne_zero.mpr hAB
        field_simp at hrosXAB ⊢
        rw[dist_comm B X]
        rw[angle_comm B A X]
        rw[mul_comm]
        rw[hrosXAB]
      _= dist C X / dist A C * (∠ A X C).sin := by sorry
      _= (∠ X A C).sin := by
        have hrosXAC := rule_of_sines X A C hXC hAC
        have : dist A C ≠ 0 := by exact dist_ne_zero.mpr hAC
        field_simp at hrosXAC ⊢
        rw[dist_comm C X]
        rw[mul_comm (∠ X A C).sin]
        rw[hrosXAC]
    -- applying theorem that on specific interval equality of
    -- sines implies equality of angles
    apply injectivity_of_sines_on_interval
    · exact angle_nonneg B A X
    · exact angle_nonneg X A C
    · calc
       ∠ B A X + ∠ X A C = ∠ B A C := by
         -- use that X is between B and C
         sorry
       _< π := by
        apply angle_lt_pi_of_not_collinear
        convert hCol using 2
        aesop
    · apply H
  · intro h1
    have hXAC : ∠ X A C ≠ 0 := by
      rw[← h1]
      rw[angle_comm]
      exact hXAB
    have hXACpi : ∠ X A C ≠ π := by
      rw[← h1]
      rw[angle_comm]
      exact hXABpi
    have hAXB : ∠ A X B ≠ 0 := by sorry
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

lemma exists_bisector_point : ∃ (D : P) , (∠ B A D = ∠ D A C) ∧ (Collinear ℝ ({B, C, D} : Set P)) := by sorry

lemma exists_point_intersection_two_lines_as_needed (X : P) (hangleatA : ∠ B A X = ∠ X A C) (hangleatB : ∠ A B X = ∠ X B C) : ∃ (F :P) , (Collinear ℝ ({C, X, F} : Set P)) ∧ (Wbtw ℝ A F B) := by sorry

theorem exists_incentre (X : P) (hangleatA : ∠ B A X = ∠ X A C) (hangleatB : ∠ A B X = ∠ X B C) : ∠ A C X = ∠ X C B := by
  by_cases hCol : Collinear ℝ ({A, B, C}: Set P)
  · sorry
  rcases exists_bisector_point A B C with ⟨ D, hD1 , hD2 ⟩
  rcases exists_bisector_point B A C with ⟨ E, hE1 , hE2 ⟩
  rcases exists_point_intersection_two_lines_as_needed A B C X hangleatA hangleatB with ⟨ F, hCXFcol , hAFBbetween ⟩
  have hCX : dist C X ≠ 0 := sorry
  have hFX : dist F X ≠ 0 := sorry
  have hAF : dist A F ≠ 0 := sorry
  have hBF : dist B F ≠ 0 := sorry
  have hangleatAshort : ∠ F A X = ∠ X A C := sorry
  have hangleatBshort : ∠ F B X = ∠ X B C := sorry
  have hangleatCAshort: ∠ A C X = ∠ A C F := sorry
  have hangleatCBshort: ∠ X C B = ∠ F C B := sorry
  have hAFCnotcol : ¬ (Collinear ℝ ({A, F, C} : Set P)) := sorry
  have hBFCnotcol : ¬ (Collinear ℝ ({B, F, C} : Set P)) := sorry
  have hFXCcol : (Collinear ℝ ({F, X, C} : Set P)) := by
    have : ({F, X, C} : Set P) = {C, X, F} := by aesop
    rw[this]
    exact hCXFcol
  have hFXCbetween : (Wbtw ℝ F X C):= by sorry
  have hCABnotcol : ¬ (Collinear ℝ ({C, A, B} : Set P)) := by
    have : ({C, A, B} : Set P) = {A, B, C} := by aesop
    rw[this]
    exact hCol
  have h1 := (angle_bisector A F C X hAFCnotcol hFXCbetween).2 hangleatAshort
  have h2 := (angle_bisector B F C X hBFCnotcol hFXCbetween).2 hangleatBshort
  have := angle_bisector C A B F hCABnotcol hAFBbetween
  rw[hangleatCAshort, hangleatCBshort, ← this]
  have h1 : dist A C / dist A F = dist C X / dist F X := by
    field_simp at h1 ⊢
    symm
    rw[mul_comm]
    exact h1
  have h2 : dist B C / dist B F = dist C X / dist F X := by
    field_simp at h2 ⊢
    symm
    rw[mul_comm]
    exact h2
  rw[dist_comm, h1, dist_comm C B, h2]
-- theorem exists_incentre' :

theorem morley (X Y Z : P) (hA1 : ∠ B A X = ∠ X A Z) (hA2 : ∠ X A Z = ∠ Z A C) (hB1 : ∠ A B X = ∠ X B Y) (hB2 : ∠ X B Y = ∠ Y B C) (hC1 : ∠ B C Y = ∠ Y C Z) (hC2 : ∠ Y C Z = ∠ Z C A) : dist X Y = dist Y Z ∧ dist Y Z = dist Z X := by sorry
