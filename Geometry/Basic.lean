
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Data.Real.Sign

open EuclideanGeometry Real FiniteDimensional AffineSubspace Affine.Simplex

/-- The sine function is injective for nonnegative angles whose sum is less than pi. -/
theorem injectivity_of_sines_on_interval (x y : ℝ) (h1x: x ≥ 0)
    (h1y: y ≥ 0)(h2: x + y < π)(h3: x.sin = y.sin): x=y := by
  wlog hxy : x ≤ y
  · rw [add_comm] at h2
    push_neg at hxy
    symm
    exact this y x h1y h1x h2 h3.symm hxy.le
  have hhalf : x ≤ π / 2 := by
    linarith
  have hineq :  y < π -x := by
    linarith
  by_cases hy : y < π / 2
  · by_contra h
    have hsinxy : x.sin < y.sin := by
      apply Real.strictMonoOn_sin
      · simp
        constructor
        · linarith
        · exact hhalf
      · simp
        constructor
        · linarith
        · exact hy.le
      push_neg at h
      exact lt_of_le_of_ne hxy h
    have := hsinxy.ne
    contradiction
  · push_neg at hy
    by_contra h
    rw [← sin_pi_sub y] at h3
    have hsinyx : x.sin < (π  - y).sin := by
      apply Real.strictMonoOn_sin
      · simp
        constructor
        · linarith
        · exact hhalf
      · simp
        constructor
        · linarith
        · linarith
      linarith
    have := hsinyx.ne
    contradiction



variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

[Fact (finrank ℝ V = 2)] (A B C : P)
[Module.Oriented ℝ V (Fin 2)]

#check oangle_add
#check Wbtw.oangle_sign_eq_of_ne_right
#check oangle_eq_angle_of_sign_eq_one
#check oangle_eq_neg_angle_of_sign_eq_neg_one

theorem angle_add_of_wbtw (X : P) (between : Wbtw ℝ A B C) (hAX : A ≠ X) (hBX : B ≠ X) (hCX: C ≠ X) : ∠ A X B + ∠ B X C = ∠ A X C := by
  by_cases hBC : B = C
  · rw [hBC, angle_self_of_ne hCX, add_zero]
  by_cases hBA : B = A
  · rw [hBA, angle_self_of_ne hAX, zero_add]
  push_neg at hBC hBA
  have signeq := Wbtw.oangle_sign_eq_of_ne_right X between hBC
  rw [wbtw_comm] at between
  have signeq' := Wbtw.oangle_sign_eq_of_ne_right X between hBA
  rw [← oangle_swap₁₃_sign, ← oangle_swap₁₃_sign A, neg_inj] at signeq'
  by_cases hsign : (∡ A X B).sign = 1
  · have hsign' : (∡ B X C ).sign = 1 := by rw [signeq, ← signeq', hsign]
    have hsign'' : (∡ A X C ).sign = 1 := by rw [← signeq', hsign]
    have := oangle_add hAX hBX hCX
    rw [oangle_eq_angle_of_sign_eq_one hsign, oangle_eq_angle_of_sign_eq_one hsign', oangle_eq_angle_of_sign_eq_one hsign'', ← Angle.coe_add] at this
    sorry -- work with quotient, need to show that sum ≤ π
  · push_neg at hsign
    unfold Angle.sign at hsign
    unfold SignType.sign at hsign
    simp at hsign
    sorry --do basically the same as above

/-- easy to prove from Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius; is switching from oriented to unoriented angle-/
theorem Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius
    (t : Affine.Triangle ℝ P) {i₁ : Fin 3} {i₂ : Fin 3} {i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.points i₃) / (angle (t.points i₁) (t.points i₂) (t.points i₃)).sin
    = 2 * Affine.Simplex.circumradius t :=
  sorry

/-- If three points are not collinear then they are affine independent. -/
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


/-- Rule of sines at the angles at A and B.-/
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

/-- Showing how to get the rule of sines at other angles. -/
example (hBA: B ≠ A) (hCA : C ≠ A): dist A C / sin (∠ A B C) = dist A B / sin (∠ A C B) := by
  have := rule_of_sines B C A hBA hCA
  rw [dist_comm, dist_comm A, angle_comm, angle_comm A]
  exact this

/-- Angle bisector theorem: an angle bisector of a triangle divides the opposite sides in the ratio of the two adjacent sides. -/
theorem angle_bisector (X : P) (hCol : ¬ Collinear ℝ ({A, B, C}: Set P))(hbetween : Wbtw ℝ B X C) : dist A B / dist B X = dist A C / dist C X ↔ ∠ B A X = ∠ X A C := by
  have h2 : Collinear ℝ ({B, X, C} : Set P) := Wbtw.collinear hbetween
  have hAB : A ≠ B := ne₁₂_of_not_collinear hCol
  have hBC : B ≠ C := ne₂₃_of_not_collinear hCol
  have hAC : A ≠ C := ne₁₃_of_not_collinear hCol
  have hCA : C ≠ A := hAC.symm
  -- the proofs of these depend on the direction of the proof, need to restructure this section
  have hXB : X ≠ B := by sorry -- stupid
  have hXC : X ≠ C := by sorry -- stupid
  have hXA : X ≠ A := by sorry -- stupid
  have hsbetween: Sbtw ℝ B X C := by
    unfold Sbtw
    exact ⟨hbetween, hXB, hXC⟩
  --all about XAB
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
  have hXAB : ∠ X A B ≠ 0 := by apply angle_ne_zero_of_not_collinear hXABnotcol
  have hXABpi : ∠ X A B ≠ π := by apply angle_ne_pi_of_not_collinear hXABnotcol
  have h3 : (∠ X A B).sin ≠ 0 := by
    intro noth3
    rw[sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]at noth3
    rcases noth3 with noth31 | noth32
    · contradiction
    · contradiction
  -- all about AXB
  have hAXBnotcol : ¬ Collinear ℝ ({A, X, B}: Set P) := by
    have : ({A, X, B} : Set P) = {X, A, B} := by aesop
    rw[this]
    exact hXABnotcol
  have hAXB : ∠ A X B ≠ 0 := by apply angle_ne_zero_of_not_collinear hAXBnotcol
  have hAXBpi : ∠ A X B ≠ π := by apply angle_ne_pi_of_not_collinear hAXBnotcol
  have h4 : (∠ A X B).sin ≠ 0 := by
    intro noth4
    rw[sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]at noth4
    rcases noth4 with noth41 | noth42
    · contradiction
    · contradiction
--all about AXC
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
  have h6 : (∠ A X C).sin ≠ 0 := by
    intro noth6
    rw[sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]at noth6
    rcases noth6 with noth61 | noth62
    · contradiction
    · contradiction
-- all about XAC
  have hXACnotcol : ¬ Collinear ℝ ({X, A, C}: Set P) := by
    have : ({X, A, C}: Set P) = {A, X, C} := by aesop
    rw [this]
    exact hAXCnotcol
  have hXAC : ∠ X A C ≠ 0 := by apply angle_ne_zero_of_not_collinear hXACnotcol
  have hXACpi : ∠ X A C ≠ π := by apply angle_ne_pi_of_not_collinear hXACnotcol
  have h5 : (∠ X A C).sin ≠ 0 := by
    intro noth5
    rw[sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]at noth5
    rcases noth5 with noth51 | noth52
    · contradiction
    · contradiction
 --all about BXC
  have hBXC : ∠ B X C ≠ 0 := by
    have := Sbtw.angle₁₂₃_eq_pi hsbetween
    rw [this]
    exact pi_ne_zero
  have sineq : (∠ A X B).sin = (∠ A X C).sin := by
    rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi] at h2
    simp only [hXB.symm, hXC.symm, false_or] at h2
    rcases h2 with h2a | h2b
    · contradiction
    rw [← sin_pi_sub]
    congrm sin ?_
    have := angle_add_angle_eq_pi_of_angle_eq_pi A h2b
    linarith
  constructor
  -- forwards direction starts here
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
      _= dist C X / dist A C * (∠ A X C).sin := by
        congrm ?_ * ?_
        · exact (div_eq_div_iff_comm (dist A B) (dist B X) (dist A C)).mp h
        · rw[sineq]

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
        exact angle_add_of_wbtw B X C A hbetween hAB.symm hXA hCA
       _< π := by
        apply angle_lt_pi_of_not_collinear
        convert hCol using 2
        aesop
    · apply H

  -- backwards direction starts here
  · intro h1
    have hXAC : ∠ X A C ≠ 0 := by
      rw[← h1]
      rw[angle_comm]
      exact hXAB
    have hXACpi : ∠ X A C ≠ π := by
      rw[← h1]
      rw[angle_comm]
      exact hXABpi
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
        · apply sineq
        · rw [angle_comm, h1]
      _ = dist A C / dist C X := by
        have := rule_of_sines A X C hCA.symm hXC
        rw [dist_comm C]
        field_simp at this ⊢
        rw [mul_comm (∠ A X C).sin]
        exact this

/-- Auxiliary result to be proved: the bisector of an angle of the triangle intersects the opposite
side. -/
lemma exists_bisector_point : ∃ (D : P) , (∠ B A D = ∠ D A C) ∧ (Collinear ℝ ({B, C, D} : Set P)) := by sorry

/-- Auxilary result to be proved, stated in too specific a way: the line through one vertex of the
triangle and the intersection of the bisectors from the other two vertices intersects the opposite
side in between the two vertices. -/
lemma exists_point_intersection_two_lines_as_needed (X : P) (hangleatA : ∠ B A X = ∠ X A C) (hangleatB : ∠ A B X = ∠ X B C) : ∃ (F :P) , (Collinear ℝ ({C, X, F} : Set P)) ∧ (Wbtw ℝ A F B) := by sorry

#check angle_eq_left

/-- Incentre theorem: The three angle bisectors of a nondegenerate triangle intersect at a point. -/
theorem exists_incentre (X : P) (hnotCol: ¬ Collinear ℝ ({A, B, C} : Set P)) (hangleatA : ∠ B A X = ∠ X A C) (hangleatB : ∠ A B X = ∠ X B C) : ∠ A C X = ∠ X C B := by
  rcases exists_bisector_point A B C with ⟨ D, hD1 , hD2 ⟩
  rcases exists_bisector_point B A C with ⟨ E, hE1 , hE2 ⟩
  rcases exists_point_intersection_two_lines_as_needed A B C X hangleatA hangleatB with ⟨ F, hCXFcol , hAFBbetween ⟩
  have hAB := ne₁₂_of_not_collinear hnotCol
  have nsbtwABX : ¬ Sbtw ℝ A B X := by sorry
  have nsbtwAXB : ¬ Sbtw ℝ A X B := by sorry
  have hCX : dist C X ≠ 0 := by
    rw [dist_ne_zero]
    intro XeqC
    have : X ≠ A := by
      intro XeqA
      have : Collinear ℝ {A, B, C} := by
        rw [XeqC, XeqA.symm]
        have : ({X, B, X} : Set P) = {B, X} := by simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff, or_true, Set.insert_eq_of_mem]
        rw [this]
        exact collinear_pair ℝ B X
      contradiction
    have : ∠ X A C = 0 := by
      rw [XeqC]
      exact angle_self_of_ne this
    rw [← hangleatA, angle_eq_zero_iff_eq_and_ne_or_sbtw] at this
    rcases this with BeqX | hABX | hAXB
    · have : Collinear ℝ {A, B, C} := by
        rw [XeqC, BeqX.1]
        have : ({A, X, X} : Set P) = {A, X} := by simp only [Set.mem_singleton_iff,
          Set.insert_eq_of_mem]
        rw [this]
        exact collinear_pair ℝ A X
      contradiction
    · contradiction
    · contradiction
  have hFX : dist F X ≠ 0 := by
    rw [dist_ne_zero]
    intro FeqX
    rw [FeqX] at hAFBbetween
    unfold Sbtw at nsbtwAXB
    simp only [hAFBbetween, ne_eq, true_and, not_and_or, not_not] at nsbtwAXB
    rcases nsbtwAXB with XeqA | XeqB
    · rw [XeqA, angle_self_of_ne hAB] at hangleatB
      exact hnotCol (collinear_of_angle_eq_zero hangleatB.symm)
    · rw [XeqB, angle_self_of_ne hAB.symm] at hangleatA
      have col := collinear_of_angle_eq_zero hangleatA.symm
      have : ({B, A, C} : Set P) = {A, B, C} := by aesop
      rw [this] at col
      contradiction
  have hAF : dist A F ≠ 0 := sorry --these should hopefully work similarly
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
    exact hnotCol
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

/-- Morley's theorem: certain intersections of angle trisectors of a triangle form an equilateral
triangle. -/
theorem morley (X Y Z : P) (hA1 : ∠ B A X = ∠ X A Z) (hA2 : ∠ X A Z = ∠ Z A C) (hB1 : ∠ A B X = ∠ X B Y) (hB2 : ∠ X B Y = ∠ Y B C) (hC1 : ∠ B C Y = ∠ Y C Z) (hC2 : ∠ Y C Z = ∠ Z C A) : dist X Y = dist Y Z ∧ dist Y Z = dist Z X := by sorry
