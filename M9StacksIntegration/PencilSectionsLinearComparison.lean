module

public import M9StacksIntegration.PencilMemberDivisor
public import M9StacksIntegration.ExteriorEvaluation
import all StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# The original pencil sections and their actual linear comparison

The native bare section comparison and the public linear section
comparison are the same original right-derived-zero map. This pins the
original series sections to linear combinations in the original H0.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace M9Native.PencilSectionsLinearComparison

/-- This compares the two actual maps, not arbitrary line identifications. -/
theorem bare_eq_linear {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (L : X.Modules)
    (x : cohomologyOverField K f L 0) :
    cohomologyOverFieldZeroEquivSections K f L x =
      (cohomologyOverFieldZeroLinearIso K f L).hom x := by
  with_unfolding_all rfl

/-- The actual original pencil basis sections have the public linear
H0 comparison, with the original cohomology classes unchanged. -/
theorem seriesSections_eq_linear {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (A : LinearSeries K f hdim d 1) (b : Module.Basis (Fin 2) K A.V) (i : Fin 2) :
    Stacks.LinearSeriesMorphism.seriesSections A b i =
      (cohomologyOverFieldZeroLinearIso K f A.L).hom
        (b i : cohomologyOverField K f A.L 0) :=
  bare_eq_linear f A.L _

/-- A member of the original pencil expands in its original two basis
sections with the actual structural-ring coefficients. -/
theorem memberSection_basis_expansion {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (A : LinearSeries K f hdim d 1) (b : Module.Basis (Fin 2) K A.V) (x : A.V) :
    PencilMemberDivisor.memberSection f hdim A x =
      ∑ i : Fin 2, ExteriorEvaluation.baseRingMap K f (b.repr x i) •
        Stacks.LinearSeriesMorphism.seriesSections A b i := by
  let F := ExteriorEvaluation.h0SectionsSemilinear K f A.L
  have hc : (x : cohomologyOverField K f A.L 0) =
      ∑ i : Fin 2, b.repr x i • (b i : cohomologyOverField K f A.L 0) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (b.sum_repr x).symm
  calc
    PencilMemberDivisor.memberSection f hdim A x =
        F (∑ i : Fin 2, b.repr x i • (b i : cohomologyOverField K f A.L 0)) :=
      congrArg F hc
    _ = ∑ i : Fin 2, ExteriorEvaluation.baseRingMap K f (b.repr x i) •
        F (b i : cohomologyOverField K f A.L 0) := by
      simp only [map_sum, map_smulₛₗ]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [seriesSections_eq_linear]
      rfl

end M9Native.PencilSectionsLinearComparison
