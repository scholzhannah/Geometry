import Mathlib.Geometry.Euclidean.Triangle

open EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
[Fact (finrank ℝ V = 2)] (A B C : P)

#check ∠ A B C

theorem angle_bisector (X : P) (h1 : ∠ B A X = ∠ X A C) (h2 : Collinear ℝ ({B, X, C} : Set P)) : dist A B / dist B X = dist A C / dist C X := by sorry

theorem exists_incentre : ∃ (X : P), (∠ B A X = ∠ X A C) ∧ (∠ A C X = ∠ X C B) ∧ (∠ C B X = ∠ X B A) := by sorry

-- theorem exists_incentre' :

theorem morley (X Y Z : P) (hA1 : ∠ B A X = ∠ X A Z) (hA2 : ∠ X A Z = ∠ Z A C) (hB1 : ∠ A B X = ∠ X B Y) (hB2 : ∠ X B Y = ∠ Y B C) (hC1 : ∠ B C Y = ∠ Y C Z) (hC2 : ∠ Y C Z = ∠ Z C A) : dist X Y = dist Y Z ∧ dist Y Z = dist Z X := by sorry
