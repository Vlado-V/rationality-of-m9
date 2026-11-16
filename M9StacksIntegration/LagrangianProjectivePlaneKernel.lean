module

public import M9StacksIntegration.LagrangianProjectiveLinearForms
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.HomogeneousIdealSheaf
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.KerQuotient

/-! The actual ideal sheaf of the native quotient projective plane,
computed by its five literal homogeneous linear equations on every
degree-one standard affine chart. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory Module
open AlgebraicGeometry.ProjectiveSpaceOfModule
open M9Native.LagrangianProjectiveIntersection M9Native.LagrangianProjectiveLinearForms
open scoped BigOperators

universe u

namespace M9Native.LagrangianProjectivePlaneKernel

variable (K : Type u) [Field K] (L : Coordinates K →ₗ[K] (Fin 5 → K))

abbrev sourceGrading := fun n : ℕ => SymPow.symmetricPower n K (Forms K)
abbrev targetGrading := fun n : ℕ => SymPow.symmetricPower n K (Forms K ⧸ constraints K L)

def homogeneousKernel : HomogeneousIdeal (sourceGrading K) :=
  Stacks.GradedKerQuotient.homogeneousKer (sourceGrading K) (targetGrading K L)
    (quotientGradedHom K (Forms K) (constraints K L))

theorem homogeneousKernel_generated_by_five : (homogeneousKernel K L).toIdeal =
    Ideal.span (Set.range (fiveForms K L)) :=
  quotientGradedHom_kernel K L

theorem rowForms_matrix_expansion (A : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    rowForms K A.mulVecLin j =
      ∑ i : Fin 14, A j i • (Pi.basisFun K (Fin 14)).dualBasis i := by
  ext w
  simp [rowForms, Pi.single_apply]

/-- The five forms retain the literal matrix entries in the fixed
fourteen-coordinate dual basis. -/
theorem fiveForms_matrix_expansion (A : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    fiveForms K A.mulVecLin j = ∑ i : Fin 14,
      A j i • SymmetricAlgebra.ι K (Forms K) ((Pi.basisFun K (Fin 14)).dualBasis i) := by
  rw [fiveForms, rowForms_matrix_expansion]
  simp only [map_sum, map_smul]

/-- Equality of actual scheme ideal sheaves for the actual native Proj
quotient embedding, derived from the graded kernel's first isomorphism. -/
theorem quotientMap_kernel : (quotientMap K (Forms K) (constraints K L)).ker =
    AlgebraicGeometry.ProjectiveSpectrum.Proj.homogeneousIdealSheaf (sourceGrading K)
      (homogeneousKernel K L) := by
  have h := Stacks.GradedKerQuotient.projMap_eq (sourceGrading K) (targetGrading K L)
    (quotientGradedHom K (Forms K) (constraints K L))
    (SymPow.surjective_gradedSymAlgMap (constraints K L).mkQ (constraints K L).mkQ_surjective)
    (Proj.irrelevant_le_map_of_surjective _ (surjective_gradedSymAlgMap_mkQ (constraints K L)))
  change (Proj.map (quotientGradedHom K (Forms K) (constraints K L)) _).ker = _
  rw [h, Scheme.Hom.ker_comp_of_isIso]
  rfl

/-- Every actual degree-one affine chart has the five actual linear
fractions as generators of the actual closed-plane embedding ideal. -/
theorem quotientMap_kernel_on_chart {f : SymmetricAlgebra K (Forms K)}
    (hf : f ∈ sourceGrading K 1) :
    ((quotientMap K (Forms K) (constraints K L)).ker).ideal
        ⟨Proj.basicOpen (sourceGrading K) f,
          Proj.isAffineOpen_basicOpen (sourceGrading K) f hf Nat.one_pos⟩ =
      Ideal.span (Set.range fun j : Fin 5 =>
        AlgebraicGeometry.ProjectiveSpectrum.Proj.chartFraction (sourceGrading K) hf 1
          ⟨fiveForms K L j, fiveForms_homogeneous_one K L j⟩) := by
  rw [quotientMap_kernel]
  exact AlgebraicGeometry.ProjectiveSpectrum.Proj.homogeneousIdealSheaf_ideal_basicOpen_eq_span_range
    (sourceGrading K) (homogeneousKernel K L) hf Nat.one_pos
    (fiveForms K L) (fun _ => 1) (fun j => fiveForms_homogeneous_one K L j)
    (homogeneousKernel_generated_by_five K L)

end M9Native.LagrangianProjectivePlaneKernel
