module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Independence of successively nonzero hyperplane coefficients

For successive genuine cuts, restriction to the previous cut annihilates
earlier equations and does not annihilate the next equation.  This
triangular separation proves independence of the actual coefficient rows,
and hence surjectivity of their actual quotient matrix.
-/

@[expose] public section
open Function Set

universe u v w

namespace M9Native.HyperplaneCoefficientIndependence

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- Triangular restriction maps certify independence of the original
coefficient vectors, with no independence hypothesis. -/
theorem linearIndependent_of_separatingMaps {r : ℕ} (v : Fin r → V)
    (W : Fin r → Type w) [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    (F : ∀ j, V →ₗ[K] W j)
    (htri : ∀ i j, i < j → F j (v i) = 0)
    (hdiag : ∀ j, F j (v j) ≠ 0) : LinearIndependent K v := by
  induction r with
  | zero => exact linearIndependent_empty_type
  | succ r ih =>
    apply linearIndependent_finSucc'.mpr
    constructor
    · exact ih (Fin.init v) (fun j => W j.castSucc) (fun j => F j.castSucc)
        (fun i j hij => htri i.castSucc j.castSucc hij) (fun j => hdiag j.castSucc)
    · intro hmem
      have hspan : Submodule.span K (Set.range (Fin.init v)) ≤ LinearMap.ker (F (Fin.last r)) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact htri j.castSucc (Fin.last r) (Fin.castSucc_lt_last j)
      exact hdiag (Fin.last r) (hspan hmem)

/-- In particular the original independent hyperplane equations define
an actual surjective matrix quotient. -/
theorem coefficientMatrix_surjective {r m : ℕ} (v : Fin r → (Fin m → K))
    (W : Fin r → Type w) [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    (F : ∀ j, (Fin m → K) →ₗ[K] W j)
    (htri : ∀ i j, i < j → F j (v i) = 0)
    (hdiag : ∀ j, F j (v j) ≠ 0) : Function.Surjective (Matrix.mulVec v) := by
  exact (linearIndependent_of_separatingMaps v W F htri hdiag).mulVec_surjective

end M9Native.HyperplaneCoefficientIndependence
