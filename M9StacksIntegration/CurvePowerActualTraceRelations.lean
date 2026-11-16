module

public import M9StacksIntegration.CurvePowerActualDiagonalSquare
public import M9StacksIntegration.PolynomialTraceRelations

/-! Actual tautological divisor relations in the radical quotient of the
original Chow-cap degree functional. All word laws used here have been
derived from the original curve, its point graphs, and its diagonal. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u
namespace M9Native.CurvePowerActualTraceRelations

open CurvePowerChowFunctional CurvePowerPointTrace CurvePowerActualWordRelations
open CurvePowerActualDiagonalSquare CurvePowerDiagonalSelfRestriction

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

abbrev TraceQuotient (n : ℕ) := PolynomialTraceRelations.TraceQuotient (actualWordDegree k C c₀ n)

def point (n : ℕ) (i : Fin n) : TraceQuotient k C c₀ n :=
  PolynomialTraceRelations.pointClass (actualWordDegree k C c₀ n) (.inl i)

def diagonal (n : ℕ) (i j : Fin n) : TraceQuotient k C c₀ n :=
  PolynomialTraceRelations.pointClass (actualWordDegree k C c₀ n) (.inr (i,j))

def reducedDiagonal (n : ℕ) (i j : Fin n) : TraceQuotient k C c₀ n :=
  CurvePowerDiagonalAlgebra.reducedDiagonal (point k C c₀ n i) (point k C c₀ n j)
    (diagonal k C c₀ n i j)

theorem word_diagonal_swap (n : ℕ) (i j : Fin n) (tail : List (Letter n)) :
    actualWordDegree k C c₀ n (.inr (i,j) :: tail) =
      actualWordDegree k C c₀ n (.inr (j,i) :: tail) := by
  unfold actualWordDegree
  simp only [List.map_cons]
  rw [CurvePowerDiagonalMarkedRestriction.letterClass_diagonal_swap k C c₀ n i j]

theorem diagonal_swap (n : ℕ) (i j : Fin n) :
    diagonal k C c₀ n i j = diagonal k C c₀ n j i := by
  have h := PolynomialTraceRelations.pointClass_self (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) 1 (.inr (i,j)) (.inr (j,i))
    (fun tail => by simpa only [one_mul] using word_diagonal_swap k C c₀ n i j tail)
  simpa only [Int.cast_one, one_mul, diagonal] using h

include hC

theorem word_point_diagonal_right (n : ℕ) (i j : Fin n) (tail : List (Letter n)) :
    actualWordDegree k C c₀ n (.inl j :: .inr (i,j) :: tail) =
      actualWordDegree k C c₀ n (.inl i :: .inl j :: tail) := by
  have hs : actualWordDegree k C c₀ n (.inl j :: .inr (i,j) :: tail) =
      actualWordDegree k C c₀ n (.inl j :: .inr (j,i) :: tail) := by
    unfold actualWordDegree
    simp only [List.map_cons]
    rw [CurvePowerDiagonalMarkedRestriction.letterClass_diagonal_swap k C c₀ n i j]
  exact hs.trans ((word_point_diagonal k C c₀ hC n j i tail).trans
    (actualWordDegree_perm k C c₀ n _ _ (List.Perm.swap _ _ _)))

theorem point_square (n : ℕ) (i : Fin n) : point k C c₀ n i ^ 2 = 0 :=
  PolynomialTraceRelations.pointClass_square (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) (.inl i) (word_point_square k C c₀ hC n i)

theorem point_diagonal (n : ℕ) (i j : Fin n) :
    point k C c₀ n i * diagonal k C c₀ n i j = point k C c₀ n i * point k C c₀ n j :=
  PolynomialTraceRelations.pointClass_pair_eq (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) (.inl i) (.inr (i,j)) (.inl i) (.inl j)
    (word_point_diagonal k C c₀ hC n i j)

theorem point_diagonal_right (n : ℕ) (i j : Fin n) :
    point k C c₀ n j * diagonal k C c₀ n i j = point k C c₀ n i * point k C c₀ n j :=
  PolynomialTraceRelations.pointClass_pair_eq (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) (.inl j) (.inr (i,j)) (.inl i) (.inl j)
    (word_point_diagonal_right k C c₀ hC n i j)

theorem diagonal_square (n : ℕ) (i j : Fin n) :
    diagonal k C c₀ n i j ^ 2 = (selfDegree k C hC : TraceQuotient k C c₀ n) *
      point k C c₀ n i * point k C c₀ n j :=
  PolynomialTraceRelations.pointClass_diagonal_square (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) (selfDegree k C hC) (.inl i) (.inl j) (.inr (i,j))
    (word_diagonal_square k C c₀ hC n i j)

theorem diagonal_self (n : ℕ) (i : Fin n) :
    diagonal k C c₀ n i i = (selfDegree k C hC : TraceQuotient k C c₀ n) *
      point k C c₀ n i :=
  PolynomialTraceRelations.pointClass_self (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) (selfDegree k C hC) (.inr (i,i)) (.inl i)
    (word_diagonal_self k C c₀ hC n i)

theorem reducedDiagonal_square (n : ℕ) (i j : Fin n) :
    reducedDiagonal k C c₀ n i j ^ 2 =
      ((selfDegree k C hC : TraceQuotient k C c₀ n) - 2) *
        point k C c₀ n i * point k C c₀ n j :=
  PolynomialTraceRelations.reducedDiagonal_sq (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) (selfDegree k C hC) (.inl i) (.inl j) (.inr (i,j))
    (word_point_square k C c₀ hC n i) (word_point_square k C c₀ hC n j)
    (word_point_diagonal k C c₀ hC n i j) (word_point_diagonal_right k C c₀ hC n i j)
    (word_diagonal_square k C c₀ hC n i j)

end M9Native.CurvePowerActualTraceRelations
